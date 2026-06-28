// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: Lean.DocString Lean.Elab.Command Lean.Parser.Tactic.Doc
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getDocString, l_Lean_TSyntax_getId,
    l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_quickLt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Data::SMap::l_Lean_SMap_find_x3f_x27___redArg;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_levelParams;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::DocString::{
    initialize_Lean_DocString, l_Lean_findDocString_x3f, runtime_initialize_Lean_DocString,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_constants, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::l_Lean_Level_param___override;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_nestD, l_Lean_MessageData_nil, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageData_withExprHover, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_ParserExtension_instInhabitedState_default, l_Lean_Parser_parserExtension,
};
use crate::r#gen::Lean::Parser::Tactic::Doc::{
    initialize_Lean_Parser_Tactic_Doc, l_Lean_Parser_Tactic_Doc_alternativeOfTactic,
    l_Lean_Parser_Tactic_Doc_customTacticName___redArg,
    l_Lean_Parser_Tactic_Doc_getTacticExtensions, l_Lean_Parser_Tactic_Doc_isTactic,
    l_Lean_Parser_Tactic_Doc_knownTacticTagExt, l_Lean_Parser_Tactic_Doc_tacticDocExtExt,
    l_Lean_Parser_Tactic_Doc_tacticNameExt, l_Lean_Parser_Tactic_Doc_tacticTagExt,
    runtime_initialize_Lean_Parser_Tactic_Doc,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_getState___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_dec_lt, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_7, lean_apply_8, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value)
                as *mut LeanObject,
            4956078449854903522 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            77, 97, 108, 102, 111, 114, 109, 101, 100, 32, 116, 97, 99, 116, 105, 99, 32, 101, 120,
            116, 101, 110, 115, 105, 111, 110, 32, 99, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value: LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value)
                as *mut LeanObject,
            9063780239635860524 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value: LeanStringObject<2> =
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
        m_data: [96, 0],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value: LeanStringObject<18> =
    LeanStringObject {
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
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            96, 32, 105, 115, 32, 97, 110, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101,
            32, 102, 111, 114, 109, 32, 111, 102, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            77, 105, 115, 115, 105, 110, 103, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116,
            105, 111, 110, 32, 99, 111, 109, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 111, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 84, 97, 99, 116, 105, 99, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value) as *mut LeanObject,15754765584490118853 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value) as *mut LeanObject,12856976837079739520 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [118, 101, 114, 115, 111, 67, 111, 109, 109, 101, 110, 116, 66, 111, 100, 121, 0]};
static mut l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            77, 97, 108, 102, 111, 114, 109, 101, 100, 32, 39, 114, 101, 103, 105, 115, 116, 101,
            114, 95, 116, 97, 99, 116, 105, 99, 95, 116, 97, 103, 39, 32, 99, 111, 109, 109, 97,
            110, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [115, 116, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value)
                as *mut LeanObject,
            9232979286016572671 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value: LeanStringObject<20> =
    LeanStringObject {
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
            114, 101, 103, 105, 115, 116, 101, 114, 95, 116, 97, 99, 116, 105, 99, 95, 116, 97,
            103, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value)
                as *mut LeanObject,
            193457151245105103 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 82, 101, 103, 105, 115, 116, 101, 114, 84, 97, 99, 116, 105, 99, 84, 97, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value) as *mut LeanObject,15754765584490118853 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value) as *mut LeanObject,1665974055269375704 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,((( 46 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut LeanObject,((( 61 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value) as *mut LeanObject,((( 46 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value) as *mut LeanObject,((( 61 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,((( 71 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value) as *mut LeanObject,((( 71 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0: u64 = 0;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [36, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value) as *mut LeanObject,13409698996255540382 as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value:
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
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value:
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
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value
        ) as *mut LeanObject,
        16145843736367156323 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value: LeanClosureObject<
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value: LeanClosureObject<
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value)
        as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Level_param___override as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value
) as *mut LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 128, 162, 32, 0]};
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value
) as *mut LeanObject;
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 4, m_data: [32, 226, 128, 148, 32, 34, 0]};
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value
) as *mut LeanObject;
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [34, 0]};
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value
) as *mut LeanObject;
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value
) as *mut LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value) as *mut LeanObject] };
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value
) as *mut LeanObject;
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value: LeanStringObject<
    17,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        65, 118, 97, 105, 108, 97, 98, 108, 101, 32, 116, 97, 103, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [112, 114, 105, 110, 116, 84, 97, 99, 84, 97, 103, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value) as *mut LeanObject,14983071855721121424 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 108, 97, 98, 80, 114, 105, 110, 116, 84, 97, 99, 84, 97, 103, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value) as *mut LeanObject,15754765584490118853 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value) as *mut LeanObject,9256493848752694986 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [68, 105, 115, 112, 108, 97, 121, 115, 32, 97, 108, 108, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 116, 97, 99, 116, 105, 99, 32, 116, 97, 103, 115, 44, 32, 119, 105, 116, 104, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 46, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 98 as usize) << 1) | 1) as *mut LeanObject,((( 37 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 130 as usize) << 1) | 1) as *mut LeanObject,((( 17 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value) as *mut LeanObject,((( 37 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value) as *mut LeanObject,((( 17 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 98 as usize) << 1) | 1) as *mut LeanObject,((( 41 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 98 as usize) << 1) | 1) as *mut LeanObject,((( 57 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value) as *mut LeanObject,((( 41 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value) as *mut LeanObject,((( 57 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(
    mut v___x_3831_: *mut LeanObject,
    mut v___x_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
    mut v___y_3837_: *mut LeanObject,
    mut v___y_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    v___x_3840_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
        v___x_3831_,
        v___x_3832_,
        v___y_3837_,
        v___y_3838_,
    );
    return v___x_3840_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(
    mut v___x_3841_: *mut LeanObject,
    mut v___x_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
    mut v___y_3845_: *mut LeanObject,
    mut v___y_3846_: *mut LeanObject,
    mut v___y_3847_: *mut LeanObject,
    mut v___y_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3850_: *mut LeanObject = core::ptr::null_mut();
    v_res_3850_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(
        v___x_3841_,
        v___x_3842_,
        v___y_3843_,
        v___y_3844_,
        v___y_3845_,
        v___y_3846_,
        v___y_3847_,
        v___y_3848_,
    );
    lean_dec(v___y_3848_);
    lean_dec_ref(v___y_3847_);
    lean_dec(v___y_3846_);
    lean_dec_ref(v___y_3845_);
    lean_dec(v___y_3844_);
    lean_dec_ref(v___y_3843_);
    return v_res_3850_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    v___x_3851_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3851_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
    v___x_3853_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3853_, 0, v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    v___x_3854_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
    v___x_3855_ = lean_unsigned_to_nat(0);
    v___x_3856_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3856_, 0, v___x_3855_);
    lean_ctor_set(v___x_3856_, 1, v___x_3855_);
    lean_ctor_set(v___x_3856_, 2, v___x_3855_);
    lean_ctor_set(v___x_3856_, 3, v___x_3855_);
    lean_ctor_set(v___x_3856_, 4, v___x_3854_);
    lean_ctor_set(v___x_3856_, 5, v___x_3854_);
    lean_ctor_set(v___x_3856_, 6, v___x_3854_);
    lean_ctor_set(v___x_3856_, 7, v___x_3854_);
    lean_ctor_set(v___x_3856_, 8, v___x_3854_);
    lean_ctor_set(v___x_3856_, 9, v___x_3854_);
    return v___x_3856_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3857_ = lean_unsigned_to_nat(32);
    v___x_3858_ = lean_mk_empty_array_with_capacity(v___x_3857_);
    v___x_3859_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3859_, 0, v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3860_: usize = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    v___x_3860_ = 5usize;
    v___x_3861_ = lean_unsigned_to_nat(0);
    v___x_3862_ = lean_unsigned_to_nat(32);
    v___x_3863_ = lean_mk_empty_array_with_capacity(v___x_3862_);
    v___x_3864_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3);
    v___x_3865_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3865_, 0, v___x_3864_);
    lean_ctor_set(v___x_3865_, 1, v___x_3863_);
    lean_ctor_set(v___x_3865_, 2, v___x_3861_);
    lean_ctor_set(v___x_3865_, 3, v___x_3861_);
    lean_ctor_set_usize(v___x_3865_, 4, v___x_3860_);
    return v___x_3865_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    v___x_3866_ = lean_box(1);
    v___x_3867_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
    v___x_3868_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
    v___x_3869_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3869_, 0, v___x_3868_);
    lean_ctor_set(v___x_3869_, 1, v___x_3867_);
    lean_ctor_set(v___x_3869_, 2, v___x_3866_);
    return v___x_3869_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(
    mut v_msgData_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    v___x_3873_ = lean_st_ref_get(v___y_3871_);
    v_env_3874_ = lean_ctor_get(v___x_3873_, 0);
    lean_inc_ref(v_env_3874_);
    lean_dec(v___x_3873_);
    v___x_3875_ = lean_st_ref_get(v___y_3871_);
    v_scopes_3876_ = lean_ctor_get(v___x_3875_, 2);
    lean_inc(v_scopes_3876_);
    lean_dec(v___x_3875_);
    v___x_3877_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_3878_ = l_List_head_x21___redArg(v___x_3877_, v_scopes_3876_);
    lean_dec(v_scopes_3876_);
    v_opts_3879_ = lean_ctor_get(v___x_3878_, 1);
    lean_inc_ref(v_opts_3879_);
    lean_dec(v___x_3878_);
    v___x_3880_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2);
    v___x_3881_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5);
    v___x_3882_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3882_, 0, v_env_3874_);
    lean_ctor_set(v___x_3882_, 1, v___x_3880_);
    lean_ctor_set(v___x_3882_, 2, v___x_3881_);
    lean_ctor_set(v___x_3882_, 3, v_opts_3879_);
    v___x_3883_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3883_, 0, v___x_3882_);
    lean_ctor_set(v___x_3883_, 1, v_msgData_3870_);
    v___x_3884_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3884_, 0, v___x_3883_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(
    mut v_msgData_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3888_: *mut LeanObject = core::ptr::null_mut();
    v_res_3888_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_3885_, v___y_3886_);
    lean_dec(v___y_3886_);
    return v_res_3888_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    v___x_3889_ = lean_box(1);
    v___x_3890_ = l_Lean_MessageData_ofFormat(v___x_3889_);
    return v___x_3890_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    v___x_3894_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2;
    v___x_3895_ = l_Lean_MessageData_ofFormat(v___x_3894_);
    return v___x_3895_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(
    mut v_x_3896_: *mut LeanObject,
    mut v_x_3897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v_before_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_unused_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3897_) == 0 {
                    return v_x_3896_;
                } else {
                    v_head_3898_ = lean_ctor_get(v_x_3897_, 0);
                    v_tail_3899_ = lean_ctor_get(v_x_3897_, 1);
                    v_isSharedCheck_3921_ = (!lean_is_exclusive(v_x_3897_)) as u8;
                    if v_isSharedCheck_3921_ == 0 {
                        v___x_3901_ = v_x_3897_;
                        v_isShared_3902_ = v_isSharedCheck_3921_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3899_);
                        lean_inc(v_head_3898_);
                        lean_dec(v_x_3897_);
                        v___x_3901_ = lean_box(0);
                        v_isShared_3902_ = v_isSharedCheck_3921_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3903_ = lean_ctor_get(v_head_3898_, 0);
                v_isSharedCheck_3919_ = (!lean_is_exclusive(v_head_3898_)) as u8;
                if v_isSharedCheck_3919_ == 0 {
                    v_unused_3920_ = lean_ctor_get(v_head_3898_, 1);
                    lean_dec(v_unused_3920_);
                    v___x_3905_ = v_head_3898_;
                    v_isShared_3906_ = v_isSharedCheck_3919_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_3903_);
                    lean_dec(v_head_3898_);
                    v___x_3905_ = lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3907_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_3906_ == 0 {
                    lean_ctor_set_tag(v___x_3905_, 7);
                    lean_ctor_set(v___x_3905_, 1, v___x_3907_);
                    lean_ctor_set(v___x_3905_, 0, v_x_3896_);
                    v___x_3909_ = v___x_3905_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_x_3896_);
                    lean_ctor_set(v_reuseFailAlloc_3918_, 1, v___x_3907_);
                    v___x_3909_ = v_reuseFailAlloc_3918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3910_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_3902_ == 0 {
                    lean_ctor_set_tag(v___x_3901_, 7);
                    lean_ctor_set(v___x_3901_, 1, v___x_3910_);
                    lean_ctor_set(v___x_3901_, 0, v___x_3909_);
                    v___x_3912_ = v___x_3901_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3909_);
                    lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3910_);
                    v___x_3912_ = v_reuseFailAlloc_3917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3913_ = l_Lean_MessageData_ofSyntax(v_before_3903_);
                v___x_3914_ = l_Lean_indentD(v___x_3913_);
                v___x_3915_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3915_, 0, v___x_3912_);
                lean_ctor_set(v___x_3915_, 1, v___x_3914_);
                v_x_3896_ = v___x_3915_;
                v_x_3897_ = v_tail_3899_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(
    mut v_opts_3922_: *mut LeanObject,
    mut v_opt_3923_: *mut LeanObject,
) -> u8 {
    let mut v_name_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    v_name_3924_ = lean_ctor_get(v_opt_3923_, 0);
    v_defValue_3925_ = lean_ctor_get(v_opt_3923_, 1);
    v_map_3926_ = lean_ctor_get(v_opts_3922_, 0);
    v___x_3927_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3926_,
            v_name_3924_,
        );
    if lean_obj_tag(v___x_3927_) == 0 {
        let mut v___x_3928_: u8 = 0;
        v___x_3928_ = (lean_unbox(v_defValue_3925_) as u8);
        return v___x_3928_;
    } else {
        let mut v_val_3929_: *mut LeanObject = core::ptr::null_mut();
        v_val_3929_ = lean_ctor_get(v___x_3927_, 0);
        lean_inc(v_val_3929_);
        lean_dec_ref_known(v___x_3927_, 1);
        if lean_obj_tag(v_val_3929_) == 1 {
            let mut v_v_3930_: u8 = 0;
            v_v_3930_ = lean_ctor_get_uint8(v_val_3929_, 0 as u32);
            lean_dec_ref_known(v_val_3929_, 0);
            return v_v_3930_;
        } else {
            let mut v___x_3931_: u8 = 0;
            lean_dec(v_val_3929_);
            v___x_3931_ = (lean_unbox(v_defValue_3925_) as u8);
            return v___x_3931_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(
    mut v_opts_3932_: *mut LeanObject,
    mut v_opt_3933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3934_: u8 = 0;
    let mut v_r_3935_: *mut LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_3932_, v_opt_3933_);
    lean_dec_ref(v_opt_3933_);
    lean_dec_ref(v_opts_3932_);
    v_r_3935_ = lean_box((v_res_3934_) as usize);
    return v_r_3935_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1;
    v___x_3940_ = l_Lean_MessageData_ofFormat(v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(
    mut v_msgData_3941_: *mut LeanObject,
    mut v_macroStack_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: u8 = 0;
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_unused_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3945_ = lean_st_ref_get(v___y_3943_);
                v_scopes_3946_ = lean_ctor_get(v___x_3945_, 2);
                lean_inc(v_scopes_3946_);
                lean_dec(v___x_3945_);
                v___x_3947_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3948_ = l_List_head_x21___redArg(v___x_3947_, v_scopes_3946_);
                lean_dec(v_scopes_3946_);
                v_opts_3949_ = lean_ctor_get(v___x_3948_, 1);
                lean_inc_ref(v_opts_3949_);
                lean_dec(v___x_3948_);
                v___x_3950_ = l_Lean_Elab_pp_macroStack;
                v___x_3951_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_3949_, v___x_3950_);
                lean_dec_ref(v_opts_3949_);
                if v___x_3951_ == 0 {
                    lean_dec(v_macroStack_3942_);
                    v___x_3952_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3952_, 0, v_msgData_3941_);
                    return v___x_3952_;
                } else {
                    if lean_obj_tag(v_macroStack_3942_) == 0 {
                        v___x_3953_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3953_, 0, v_msgData_3941_);
                        return v___x_3953_;
                    } else {
                        v_head_3954_ = lean_ctor_get(v_macroStack_3942_, 0);
                        lean_inc(v_head_3954_);
                        v_after_3955_ = lean_ctor_get(v_head_3954_, 1);
                        v_isSharedCheck_3970_ = (!lean_is_exclusive(v_head_3954_)) as u8;
                        if v_isSharedCheck_3970_ == 0 {
                            v_unused_3971_ = lean_ctor_get(v_head_3954_, 0);
                            lean_dec(v_unused_3971_);
                            v___x_3957_ = v_head_3954_;
                            v_isShared_3958_ = v_isSharedCheck_3970_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3955_);
                            lean_dec(v_head_3954_);
                            v___x_3957_ = lean_box(0);
                            v_isShared_3958_ = v_isSharedCheck_3970_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3959_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_3958_ == 0 {
                    lean_ctor_set_tag(v___x_3957_, 7);
                    lean_ctor_set(v___x_3957_, 1, v___x_3959_);
                    lean_ctor_set(v___x_3957_, 0, v_msgData_3941_);
                    v___x_3961_ = v___x_3957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_msgData_3941_);
                    lean_ctor_set(v_reuseFailAlloc_3969_, 1, v___x_3959_);
                    v___x_3961_ = v_reuseFailAlloc_3969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3962_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2);
                v___x_3963_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3963_, 0, v___x_3961_);
                lean_ctor_set(v___x_3963_, 1, v___x_3962_);
                v___x_3964_ = l_Lean_MessageData_ofSyntax(v_after_3955_);
                v___x_3965_ = l_Lean_indentD(v___x_3964_);
                v_msgData_3966_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3966_, 0, v___x_3963_);
                lean_ctor_set(v_msgData_3966_, 1, v___x_3965_);
                v___x_3967_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(v_msgData_3966_, v_macroStack_3942_);
                v___x_3968_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3968_, 0, v___x_3967_);
                return v___x_3968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(
    mut v_msgData_3972_: *mut LeanObject,
    mut v_macroStack_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
    mut v___y_3975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3976_: *mut LeanObject = core::ptr::null_mut();
    v_res_3976_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_3972_, v_macroStack_3973_, v___y_3974_);
    lean_dec(v___y_3974_);
    return v_res_3976_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(
    mut v_msg_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3996_: u8 = 0;
    let mut v_a_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3981_ = l_Lean_Elab_Command_getRef___redArg(v___y_3978_);
                if lean_obj_tag(v___x_3981_) == 0 {
                    v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
                    lean_inc(v_a_3982_);
                    lean_dec_ref_known(v___x_3981_, 1);
                    v_macroStack_3983_ = lean_ctor_get(v___y_3978_, 4);
                    v___x_3984_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_3977_, v___y_3979_);
                    v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
                    lean_inc(v_a_3985_);
                    lean_dec_ref(v___x_3984_);
                    v___x_3986_ = l_Lean_Elab_getBetterRef(v_a_3982_, v_macroStack_3983_);
                    lean_dec(v_a_3982_);
                    lean_inc(v_macroStack_3983_);
                    v___x_3987_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_3985_, v_macroStack_3983_, v___y_3979_);
                    v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
                    v_isSharedCheck_3996_ = (!lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_3996_ == 0 {
                        v___x_3990_ = v___x_3987_;
                        v_isShared_3991_ = v_isSharedCheck_3996_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3988_);
                        lean_dec(v___x_3987_);
                        v___x_3990_ = lean_box(0);
                        v_isShared_3991_ = v_isSharedCheck_3996_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_3977_);
                    v_a_3997_ = lean_ctor_get(v___x_3981_, 0);
                    v_isSharedCheck_4004_ = (!lean_is_exclusive(v___x_3981_)) as u8;
                    if v_isSharedCheck_4004_ == 0 {
                        v___x_3999_ = v___x_3981_;
                        v_isShared_4000_ = v_isSharedCheck_4004_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3997_);
                        lean_dec(v___x_3981_);
                        v___x_3999_ = lean_box(0);
                        v_isShared_4000_ = v_isSharedCheck_4004_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3992_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3992_, 0, v___x_3986_);
                lean_ctor_set(v___x_3992_, 1, v_a_3988_);
                if v_isShared_3991_ == 0 {
                    lean_ctor_set_tag(v___x_3990_, 1);
                    lean_ctor_set(v___x_3990_, 0, v___x_3992_);
                    v___x_3994_ = v___x_3990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
                    v___x_3994_ = v_reuseFailAlloc_3995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3994_;
            }
            3 => {
                if v_isShared_4000_ == 0 {
                    v___x_4002_ = v___x_3999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
                    v___x_4002_ = v_reuseFailAlloc_4003_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(
    mut v_msg_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4009_: *mut LeanObject = core::ptr::null_mut();
    v_res_4009_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(
            v_msg_4005_,
            v___y_4006_,
            v___y_4007_,
        );
    lean_dec(v___y_4007_);
    lean_dec_ref(v___y_4006_);
    return v_res_4009_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(
    mut v_ref_4010_: *mut LeanObject,
    mut v_msg_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4026_: u8 = 0;
    let mut v_ref_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4015_ = l_Lean_Elab_Command_getRef___redArg(v___y_4012_);
                if lean_obj_tag(v___x_4015_) == 0 {
                    v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
                    lean_inc(v_a_4016_);
                    lean_dec_ref_known(v___x_4015_, 1);
                    v_fileName_4017_ = lean_ctor_get(v___y_4012_, 0);
                    v_fileMap_4018_ = lean_ctor_get(v___y_4012_, 1);
                    v_currRecDepth_4019_ = lean_ctor_get(v___y_4012_, 2);
                    v_cmdPos_4020_ = lean_ctor_get(v___y_4012_, 3);
                    v_macroStack_4021_ = lean_ctor_get(v___y_4012_, 4);
                    v_quotContext_x3f_4022_ = lean_ctor_get(v___y_4012_, 5);
                    v_currMacroScope_4023_ = lean_ctor_get(v___y_4012_, 6);
                    v_snap_x3f_4024_ = lean_ctor_get(v___y_4012_, 8);
                    v_cancelTk_x3f_4025_ = lean_ctor_get(v___y_4012_, 9);
                    v_suppressElabErrors_4026_ = lean_ctor_get_uint8(
                        v___y_4012_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_4027_ = l_Lean_replaceRef(v_ref_4010_, v_a_4016_);
                    lean_dec(v_a_4016_);
                    lean_inc(v_cancelTk_x3f_4025_);
                    lean_inc(v_snap_x3f_4024_);
                    lean_inc(v_currMacroScope_4023_);
                    lean_inc(v_quotContext_x3f_4022_);
                    lean_inc(v_macroStack_4021_);
                    lean_inc(v_cmdPos_4020_);
                    lean_inc(v_currRecDepth_4019_);
                    lean_inc_ref(v_fileMap_4018_);
                    lean_inc_ref(v_fileName_4017_);
                    v___x_4028_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_4028_, 0, v_fileName_4017_);
                    lean_ctor_set(v___x_4028_, 1, v_fileMap_4018_);
                    lean_ctor_set(v___x_4028_, 2, v_currRecDepth_4019_);
                    lean_ctor_set(v___x_4028_, 3, v_cmdPos_4020_);
                    lean_ctor_set(v___x_4028_, 4, v_macroStack_4021_);
                    lean_ctor_set(v___x_4028_, 5, v_quotContext_x3f_4022_);
                    lean_ctor_set(v___x_4028_, 6, v_currMacroScope_4023_);
                    lean_ctor_set(v___x_4028_, 7, v_ref_4027_);
                    lean_ctor_set(v___x_4028_, 8, v_snap_x3f_4024_);
                    lean_ctor_set(v___x_4028_, 9, v_cancelTk_x3f_4025_);
                    lean_ctor_set_uint8(
                        v___x_4028_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_4026_,
                    );
                    v___x_4029_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_4011_, v___x_4028_, v___y_4013_);
                    lean_dec_ref_known(v___x_4028_, 10);
                    return v___x_4029_;
                } else {
                    lean_dec_ref(v_msg_4011_);
                    v_a_4030_ = lean_ctor_get(v___x_4015_, 0);
                    v_isSharedCheck_4037_ = (!lean_is_exclusive(v___x_4015_)) as u8;
                    if v_isSharedCheck_4037_ == 0 {
                        v___x_4032_ = v___x_4015_;
                        v_isShared_4033_ = v_isSharedCheck_4037_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4030_);
                        lean_dec(v___x_4015_);
                        v___x_4032_ = lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4037_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4033_ == 0 {
                    v___x_4035_ = v___x_4032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
                    v___x_4035_ = v_reuseFailAlloc_4036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(
    mut v_ref_4038_: *mut LeanObject,
    mut v_msg_4039_: *mut LeanObject,
    mut v___y_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4043_: *mut LeanObject = core::ptr::null_mut();
    v_res_4043_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(
            v_ref_4038_,
            v_msg_4039_,
            v___y_4040_,
            v___y_4041_,
        );
    lean_dec(v___y_4041_);
    lean_dec_ref(v___y_4040_);
    lean_dec(v_ref_4038_);
    return v_res_4043_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6() -> *mut LeanObject {
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    v___x_4054_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5;
    v___x_4055_ = l_Lean_stringToMessageData(v___x_4054_);
    return v___x_4055_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12() -> *mut LeanObject {
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11;
    v___x_4067_ = l_Lean_stringToMessageData(v___x_4066_);
    return v___x_4067_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14() -> *mut LeanObject {
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    v___x_4069_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13;
    v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
    return v___x_4070_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16() -> *mut LeanObject {
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    v___x_4072_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15;
    v___x_4073_ = l_Lean_stringToMessageData(v___x_4072_);
    return v___x_4073_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18() -> *mut LeanObject {
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    v___x_4075_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17;
    v___x_4076_ = l_Lean_stringToMessageData(v___x_4075_);
    return v___x_4076_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabTacticExtension(
    mut v_x_4077_: *mut LeanObject,
    mut v_a_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docs_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4126_: u8 = 0;
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4142_: u8 = 0;
    let mut v___y_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: u8 = 0;
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut v_a_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4081_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4;
                lean_inc(v_x_4077_);
                v___x_4082_ = l_Lean_Syntax_isOfKind(v_x_4077_, v___x_4081_);
                if v___x_4082_ == 0 {
                    lean_dec(v_x_4077_);
                    v___x_4083_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6,
                    );
                    v___x_4084_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4083_, v_a_4078_, v_a_4079_);
                    return v___x_4084_;
                } else {
                    v___x_4085_ = lean_unsigned_to_nat(0);
                    v___x_4086_ = l_Lean_Syntax_getArg(v_x_4077_, v___x_4085_);
                    lean_inc(v___x_4086_);
                    v___x_4087_ = l_Lean_Syntax_matchesNull(v___x_4086_, v___x_4085_);
                    if v___x_4087_ == 0 {
                        v___x_4088_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_4086_);
                        v___x_4089_ = l_Lean_Syntax_matchesNull(v___x_4086_, v___x_4088_);
                        if v___x_4089_ == 0 {
                            lean_dec(v___x_4086_);
                            lean_dec(v_x_4077_);
                            v___x_4090_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once
                                ),
                                _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6,
                            );
                            v___x_4091_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4090_, v_a_4078_, v_a_4079_);
                            return v___x_4091_;
                        } else {
                            v_docs_4092_ = l_Lean_Syntax_getArg(v___x_4086_, v___x_4085_);
                            lean_dec(v___x_4086_);
                            v___x_4093_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8;
                            lean_inc(v_docs_4092_);
                            v___x_4094_ = l_Lean_Syntax_isOfKind(v_docs_4092_, v___x_4093_);
                            if v___x_4094_ == 0 {
                                lean_dec(v_docs_4092_);
                                lean_dec(v_x_4077_);
                                v___x_4095_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once
                                    ),
                                    _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6,
                                );
                                v___x_4096_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4095_, v_a_4078_, v_a_4079_);
                                return v___x_4096_;
                            } else {
                                v___x_4097_ = lean_unsigned_to_nat(2);
                                v___x_4098_ = l_Lean_Syntax_getArg(v_x_4077_, v___x_4097_);
                                lean_dec(v_x_4077_);
                                v___x_4099_ =
                                    l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10;
                                lean_inc(v___x_4098_);
                                v___x_4100_ = l_Lean_Syntax_isOfKind(v___x_4098_, v___x_4099_);
                                if v___x_4100_ == 0 {
                                    lean_dec(v___x_4098_);
                                    lean_dec(v_docs_4092_);
                                    v___x_4101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once), _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
                                    v___x_4102_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4101_, v_a_4078_, v_a_4079_);
                                    return v___x_4102_;
                                } else {
                                    v___x_4103_ = lean_box(0);
                                    lean_inc(v___x_4098_);
                                    v___f_4104_ = lean_alloc_closure(
                                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        9,
                                        2,
                                    );
                                    lean_closure_set(v___f_4104_, 0, v___x_4098_);
                                    lean_closure_set(v___f_4104_, 1, v___x_4103_);
                                    v___x_4105_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                                        v___f_4104_,
                                        v_a_4078_,
                                        v_a_4079_,
                                    );
                                    if lean_obj_tag(v___x_4105_) == 0 {
                                        v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
                                        v_isSharedCheck_4172_ =
                                            (!lean_is_exclusive(v___x_4105_)) as u8;
                                        if v_isSharedCheck_4172_ == 0 {
                                            v___x_4108_ = v___x_4105_;
                                            v_isShared_4109_ = v_isSharedCheck_4172_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4106_);
                                            lean_dec(v___x_4105_);
                                            v___x_4108_ = lean_box(0);
                                            v_isShared_4109_ = v_isSharedCheck_4172_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_4098_);
                                        lean_dec(v_docs_4092_);
                                        v_a_4173_ = lean_ctor_get(v___x_4105_, 0);
                                        v_isSharedCheck_4180_ =
                                            (!lean_is_exclusive(v___x_4105_)) as u8;
                                        if v_isSharedCheck_4180_ == 0 {
                                            v___x_4175_ = v___x_4105_;
                                            v_isShared_4176_ = v_isSharedCheck_4180_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4173_);
                                            lean_dec(v___x_4105_);
                                            v___x_4175_ = lean_box(0);
                                            v_isShared_4176_ = v_isSharedCheck_4180_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v___x_4086_);
                        v___x_4181_ = lean_unsigned_to_nat(1);
                        v_cmd_4182_ = l_Lean_Syntax_getArg(v_x_4077_, v___x_4181_);
                        lean_dec(v_x_4077_);
                        v___x_4183_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once
                            ),
                            _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18,
                        );
                        v___x_4184_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_4182_, v___x_4183_, v_a_4078_, v_a_4079_);
                        lean_dec(v_cmd_4182_);
                        return v___x_4184_;
                    }
                }
            }
            1 => {
                v___x_4159_ = lean_st_ref_get(v_a_4079_);
                v_env_4160_ = lean_ctor_get(v___x_4159_, 0);
                lean_inc_ref(v_env_4160_);
                lean_dec(v___x_4159_);
                lean_inc(v_a_4106_);
                v___x_4161_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4160_, v_a_4106_);
                if lean_obj_tag(v___x_4161_) == 1 {
                    lean_del_object(v___x_4108_);
                    lean_dec(v_docs_4092_);
                    v_val_4162_ = lean_ctor_get(v___x_4161_, 0);
                    lean_inc(v_val_4162_);
                    lean_dec_ref_known(v___x_4161_, 1);
                    v___x_4163_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12,
                    );
                    v___x_4164_ = l_Lean_MessageData_ofConstName(v_a_4106_, v___x_4087_);
                    v___x_4165_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4165_, 0, v___x_4163_);
                    lean_ctor_set(v___x_4165_, 1, v___x_4164_);
                    v___x_4166_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16,
                    );
                    v___x_4167_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4167_, 0, v___x_4165_);
                    lean_ctor_set(v___x_4167_, 1, v___x_4166_);
                    v___x_4168_ = l_Lean_MessageData_ofConstName(v_val_4162_, v___x_4087_);
                    v___x_4169_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4169_, 0, v___x_4167_);
                    lean_ctor_set(v___x_4169_, 1, v___x_4168_);
                    v___x_4170_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4170_, 0, v___x_4169_);
                    lean_ctor_set(v___x_4170_, 1, v___x_4163_);
                    v___x_4171_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_4098_, v___x_4170_, v_a_4078_, v_a_4079_);
                    lean_dec(v___x_4098_);
                    return v___x_4171_;
                } else {
                    lean_dec(v___x_4161_);
                    v___y_4154_ = v_a_4078_;
                    v___y_4155_ = v_a_4079_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_4112_ = lean_st_ref_take(v___y_4111_);
                v_env_4113_ = lean_ctor_get(v___x_4112_, 0);
                v_messages_4114_ = lean_ctor_get(v___x_4112_, 1);
                v_scopes_4115_ = lean_ctor_get(v___x_4112_, 2);
                v_usedQuotCtxts_4116_ = lean_ctor_get(v___x_4112_, 3);
                v_nextMacroScope_4117_ = lean_ctor_get(v___x_4112_, 4);
                v_maxRecDepth_4118_ = lean_ctor_get(v___x_4112_, 5);
                v_ngen_4119_ = lean_ctor_get(v___x_4112_, 6);
                v_auxDeclNGen_4120_ = lean_ctor_get(v___x_4112_, 7);
                v_infoState_4121_ = lean_ctor_get(v___x_4112_, 8);
                v_traceState_4122_ = lean_ctor_get(v___x_4112_, 9);
                v_snapshotTasks_4123_ = lean_ctor_get(v___x_4112_, 10);
                v_isSharedCheck_4142_ = (!lean_is_exclusive(v___x_4112_)) as u8;
                if v_isSharedCheck_4142_ == 0 {
                    v___x_4125_ = v___x_4112_;
                    v_isShared_4126_ = v_isSharedCheck_4142_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4123_);
                    lean_inc(v_traceState_4122_);
                    lean_inc(v_infoState_4121_);
                    lean_inc(v_auxDeclNGen_4120_);
                    lean_inc(v_ngen_4119_);
                    lean_inc(v_maxRecDepth_4118_);
                    lean_inc(v_nextMacroScope_4117_);
                    lean_inc(v_usedQuotCtxts_4116_);
                    lean_inc(v_scopes_4115_);
                    lean_inc(v_messages_4114_);
                    lean_inc(v_env_4113_);
                    lean_dec(v___x_4112_);
                    v___x_4125_ = lean_box(0);
                    v_isShared_4126_ = v_isSharedCheck_4142_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4127_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
                v_toEnvExtension_4128_ = lean_ctor_get(v___x_4127_, 0);
                v_asyncMode_4129_ = lean_ctor_get(v_toEnvExtension_4128_, 2);
                v___x_4130_ = l_Lean_TSyntax_getDocString(v_docs_4092_);
                lean_dec(v_docs_4092_);
                v___x_4131_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4131_, 0, v_a_4106_);
                lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                v___x_4132_ = lean_box(0);
                v___x_4133_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4127_,
                    v_env_4113_,
                    v___x_4131_,
                    v_asyncMode_4129_,
                    v___x_4132_,
                );
                if v_isShared_4126_ == 0 {
                    lean_ctor_set(v___x_4125_, 0, v___x_4133_);
                    v___x_4135_ = v___x_4125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4133_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 1, v_messages_4114_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 2, v_scopes_4115_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 3, v_usedQuotCtxts_4116_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 4, v_nextMacroScope_4117_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 5, v_maxRecDepth_4118_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 6, v_ngen_4119_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 7, v_auxDeclNGen_4120_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 8, v_infoState_4121_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 9, v_traceState_4122_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 10, v_snapshotTasks_4123_);
                    v___x_4135_ = v_reuseFailAlloc_4141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4136_ = lean_st_ref_set(v___y_4111_, v___x_4135_);
                v___x_4137_ = lean_box(0);
                if v_isShared_4109_ == 0 {
                    lean_ctor_set(v___x_4108_, 0, v___x_4137_);
                    v___x_4139_ = v___x_4108_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4137_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4139_;
            }
            6 => {
                if v___y_4146_ == 0 {
                    lean_dec(v___x_4098_);
                    v___y_4111_ = v___y_4145_;
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_4108_);
                    lean_dec(v_docs_4092_);
                    v___x_4147_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12,
                    );
                    v___x_4148_ = l_Lean_MessageData_ofConstName(v_a_4106_, v___x_4087_);
                    v___x_4149_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4149_, 0, v___x_4147_);
                    lean_ctor_set(v___x_4149_, 1, v___x_4148_);
                    v___x_4150_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14,
                    );
                    v___x_4151_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4151_, 0, v___x_4149_);
                    lean_ctor_set(v___x_4151_, 1, v___x_4150_);
                    v___x_4152_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_4098_, v___x_4151_, v___y_4144_, v___y_4145_);
                    lean_dec(v___x_4098_);
                    return v___x_4152_;
                }
            }
            7 => {
                v___x_4156_ = lean_st_ref_get(v___y_4155_);
                v_env_4157_ = lean_ctor_get(v___x_4156_, 0);
                lean_inc_ref(v_env_4157_);
                lean_dec(v___x_4156_);
                v___x_4158_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4157_, v_a_4106_);
                if v___x_4158_ == 0 {
                    v___y_4144_ = v___y_4154_;
                    v___y_4145_ = v___y_4155_;
                    v___y_4146_ = v___x_4100_;
                    state = 6;
                    continue;
                } else {
                    v___y_4144_ = v___y_4154_;
                    v___y_4145_ = v___y_4155_;
                    v___y_4146_ = v___x_4087_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_4176_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
                    v___x_4178_ = v_reuseFailAlloc_4179_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(
    mut v_x_4185_: *mut LeanObject,
    mut v_a_4186_: *mut LeanObject,
    mut v_a_4187_: *mut LeanObject,
    mut v_a_4188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4189_: *mut LeanObject = core::ptr::null_mut();
    v_res_4189_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_4185_, v_a_4186_, v_a_4187_);
    lean_dec(v_a_4187_);
    lean_dec_ref(v_a_4186_);
    return v_res_4189_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(
    mut v_msgData_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    v___x_4194_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_4190_, v___y_4192_);
    return v___x_4194_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(
    mut v_msgData_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4199_: *mut LeanObject = core::ptr::null_mut();
    v_res_4199_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_4195_, v___y_4196_, v___y_4197_);
    lean_dec(v___y_4197_);
    lean_dec_ref(v___y_4196_);
    return v_res_4199_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(
    mut v_00_u03b1_4200_: *mut LeanObject,
    mut v_msg_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    v___x_4205_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(
            v_msg_4201_,
            v___y_4202_,
            v___y_4203_,
        );
    return v___x_4205_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(
    mut v_00_u03b1_4206_: *mut LeanObject,
    mut v_msg_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4211_: *mut LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(
        v_00_u03b1_4206_,
        v_msg_4207_,
        v___y_4208_,
        v___y_4209_,
    );
    lean_dec(v___y_4209_);
    lean_dec_ref(v___y_4208_);
    return v_res_4211_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(
    mut v_00_u03b1_4212_: *mut LeanObject,
    mut v_ref_4213_: *mut LeanObject,
    mut v_msg_4214_: *mut LeanObject,
    mut v___y_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    v___x_4218_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(
            v_ref_4213_,
            v_msg_4214_,
            v___y_4215_,
            v___y_4216_,
        );
    return v___x_4218_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(
    mut v_00_u03b1_4219_: *mut LeanObject,
    mut v_ref_4220_: *mut LeanObject,
    mut v_msg_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4225_: *mut LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(
        v_00_u03b1_4219_,
        v_ref_4220_,
        v_msg_4221_,
        v___y_4222_,
        v___y_4223_,
    );
    lean_dec(v___y_4223_);
    lean_dec_ref(v___y_4222_);
    lean_dec(v_ref_4220_);
    return v_res_4225_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(
    mut v_msgData_4226_: *mut LeanObject,
    mut v_macroStack_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    v___x_4231_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_4226_, v_macroStack_4227_, v___y_4229_);
    return v___x_4231_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(
    mut v_msgData_4232_: *mut LeanObject,
    mut v_macroStack_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
    mut v___y_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4237_: *mut LeanObject = core::ptr::null_mut();
    v_res_4237_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_4232_, v_macroStack_4233_, v___y_4234_, v___y_4235_);
    lean_dec(v___y_4235_);
    lean_dec_ref(v___y_4234_);
    return v_res_4237_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1()
-> *mut LeanObject {
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4250_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4;
    v___x_4251_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4;
    v___x_4252_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4253_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4249_,
        v___x_4250_,
        v___x_4251_,
        v___x_4252_,
    );
    return v___x_4253_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(
    mut v_a_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4255_: *mut LeanObject = core::ptr::null_mut();
    v_res_4255_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
    return v_res_4255_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3()
-> *mut LeanObject {
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4;
    v___x_4283_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6;
    v___x_4284_ = l_Lean_addBuiltinDeclarationRanges(v___x_4282_, v___x_4283_);
    return v___x_4284_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(
    mut v_a_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4286_: *mut LeanObject = core::ptr::null_mut();
    v_res_4286_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
    return v_res_4286_;
}
pub unsafe fn _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    v___x_4288_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0;
    v___x_4289_ = l_Lean_stringToMessageData(v___x_4288_);
    return v___x_4289_;
}
pub unsafe fn l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(
    mut v_stx_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: u8 = 0;
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: u8 = 0;
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4309_ = lean_unsigned_to_nat(1);
                v___x_4310_ = l_Lean_Syntax_getArg(v_stx_4291_, v___x_4309_);
                match lean_obj_tag(v___x_4310_) {
                    2 => {
                        lean_dec(v_stx_4291_);
                        v_val_4311_ = lean_ctor_get(v___x_4310_, 1);
                        lean_inc_ref(v_val_4311_);
                        lean_dec_ref_known(v___x_4310_, 2);
                        v_val_4302_ = v_val_4311_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_kind_4312_ = lean_ctor_get(v___x_4310_, 1);
                        lean_inc(v_kind_4312_);
                        if lean_obj_tag(v_kind_4312_) == 1 {
                            v_pre_4313_ = lean_ctor_get(v_kind_4312_, 0);
                            lean_inc(v_pre_4313_);
                            if lean_obj_tag(v_pre_4313_) == 1 {
                                v_pre_4314_ = lean_ctor_get(v_pre_4313_, 0);
                                lean_inc(v_pre_4314_);
                                if lean_obj_tag(v_pre_4314_) == 1 {
                                    v_pre_4315_ = lean_ctor_get(v_pre_4314_, 0);
                                    lean_inc(v_pre_4315_);
                                    if lean_obj_tag(v_pre_4315_) == 1 {
                                        v_pre_4316_ = lean_ctor_get(v_pre_4315_, 0);
                                        if lean_obj_tag(v_pre_4316_) == 0 {
                                            v_str_4317_ = lean_ctor_get(v_kind_4312_, 1);
                                            lean_inc_ref(v_str_4317_);
                                            lean_dec_ref_known(v_kind_4312_, 2);
                                            v_str_4318_ = lean_ctor_get(v_pre_4313_, 1);
                                            lean_inc_ref(v_str_4318_);
                                            lean_dec_ref_known(v_pre_4313_, 2);
                                            v_str_4319_ = lean_ctor_get(v_pre_4314_, 1);
                                            lean_inc_ref(v_str_4319_);
                                            lean_dec_ref_known(v_pre_4314_, 2);
                                            v_str_4320_ = lean_ctor_get(v_pre_4315_, 1);
                                            lean_inc_ref(v_str_4320_);
                                            lean_dec_ref_known(v_pre_4315_, 2);
                                            v___x_4321_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0;
                                            v___x_4322_ =
                                                lean_string_dec_eq(v_str_4320_, v___x_4321_);
                                            lean_dec_ref(v_str_4320_);
                                            if v___x_4322_ == 0 {
                                                lean_dec_ref(v_str_4319_);
                                                lean_dec_ref(v_str_4318_);
                                                lean_dec_ref(v_str_4317_);
                                                lean_dec_ref_known(v___x_4310_, 3);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_4323_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1;
                                                v___x_4324_ =
                                                    lean_string_dec_eq(v_str_4319_, v___x_4323_);
                                                lean_dec_ref(v_str_4319_);
                                                if v___x_4324_ == 0 {
                                                    lean_dec_ref(v_str_4318_);
                                                    lean_dec_ref(v_str_4317_);
                                                    lean_dec_ref_known(v___x_4310_, 3);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_4325_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2;
                                                    v___x_4326_ = lean_string_dec_eq(
                                                        v_str_4318_,
                                                        v___x_4325_,
                                                    );
                                                    lean_dec_ref(v_str_4318_);
                                                    if v___x_4326_ == 0 {
                                                        lean_dec_ref(v_str_4317_);
                                                        lean_dec_ref_known(v___x_4310_, 3);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_4327_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2;
                                                        v___x_4328_ = lean_string_dec_eq(
                                                            v_str_4317_,
                                                            v___x_4327_,
                                                        );
                                                        lean_dec_ref(v_str_4317_);
                                                        if v___x_4328_ == 0 {
                                                            lean_dec_ref_known(v___x_4310_, 3);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_4329_ = lean_unsigned_to_nat(0);
                                                            v___x_4330_ = l_Lean_Syntax_getArg(
                                                                v___x_4310_,
                                                                v___x_4329_,
                                                            );
                                                            lean_dec_ref_known(v___x_4310_, 3);
                                                            if lean_obj_tag(v___x_4330_) == 2 {
                                                                lean_dec(v_stx_4291_);
                                                                v_val_4331_ =
                                                                    lean_ctor_get(v___x_4330_, 1);
                                                                lean_inc_ref(v_val_4331_);
                                                                lean_dec_ref_known(v___x_4330_, 2);
                                                                v_val_4302_ = v_val_4331_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                lean_dec(v___x_4330_);
                                                                v___x_4332_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once), _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
                                                                lean_inc(v_stx_4291_);
                                                                v___x_4333_ =
                                                                    l_Lean_MessageData_ofSyntax(
                                                                        v_stx_4291_,
                                                                    );
                                                                v___x_4334_ =
                                                                    l_Lean_indentD(v___x_4333_);
                                                                v___x_4335_ = lean_alloc_ctor(
                                                                    7,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_4335_,
                                                                    0,
                                                                    v___x_4332_,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_4335_,
                                                                    1,
                                                                    v___x_4334_,
                                                                );
                                                                v___x_4336_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_4291_, v___x_4335_, v___y_4292_, v___y_4293_);
                                                                lean_dec(v_stx_4291_);
                                                                return v___x_4336_;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref_known(v_pre_4315_, 2);
                                            lean_dec_ref_known(v_pre_4314_, 2);
                                            lean_dec_ref_known(v_pre_4313_, 2);
                                            lean_dec_ref_known(v_kind_4312_, 2);
                                            lean_dec_ref_known(v___x_4310_, 3);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_pre_4315_);
                                        lean_dec_ref_known(v_pre_4314_, 2);
                                        lean_dec_ref_known(v_pre_4313_, 2);
                                        lean_dec_ref_known(v_kind_4312_, 2);
                                        lean_dec_ref_known(v___x_4310_, 3);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_pre_4314_);
                                    lean_dec_ref_known(v_pre_4313_, 2);
                                    lean_dec_ref_known(v_kind_4312_, 2);
                                    lean_dec_ref_known(v___x_4310_, 3);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_kind_4312_, 2);
                                lean_dec(v_pre_4313_);
                                lean_dec_ref_known(v___x_4310_, 3);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_kind_4312_);
                            lean_dec_ref_known(v___x_4310_, 3);
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v___x_4310_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4296_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once), _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
                lean_inc(v_stx_4291_);
                v___x_4297_ = l_Lean_MessageData_ofSyntax(v_stx_4291_);
                v___x_4298_ = l_Lean_indentD(v___x_4297_);
                v___x_4299_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4299_, 0, v___x_4296_);
                lean_ctor_set(v___x_4299_, 1, v___x_4298_);
                v___x_4300_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_4291_, v___x_4299_, v___y_4292_, v___y_4293_);
                lean_dec(v_stx_4291_);
                return v___x_4300_;
            }
            2 => {
                v___x_4303_ = lean_unsigned_to_nat(0);
                v___x_4304_ = lean_string_utf8_byte_size(v_val_4302_);
                v___x_4305_ = lean_unsigned_to_nat(2);
                v___x_4306_ = lean_nat_sub(v___x_4304_, v___x_4305_);
                v___x_4307_ = lean_string_utf8_extract(v_val_4302_, v___x_4303_, v___x_4306_);
                lean_dec(v___x_4306_);
                lean_dec_ref(v_val_4302_);
                v___x_4308_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4308_, 0, v___x_4307_);
                return v___x_4308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(
    mut v_stx_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4341_: *mut LeanObject = core::ptr::null_mut();
    v_res_4341_ =
        l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(
            v_stx_4337_,
            v___y_4338_,
            v___y_4339_,
        );
    lean_dec(v___y_4339_);
    lean_dec_ref(v___y_4338_);
    return v_res_4341_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1() -> *mut LeanObject {
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    v___x_4343_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0;
    v___x_4344_ = l_Lean_stringToMessageData(v___x_4343_);
    return v___x_4344_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(
    mut v_x_4354_: *mut LeanObject,
    mut v_a_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_doc_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tag_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: u8 = 0;
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_user_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4414_: u8 = 0;
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: u8 = 0;
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: u8 = 0;
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4429_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5;
                lean_inc(v_x_4354_);
                v___x_4430_ = l_Lean_Syntax_isOfKind(v_x_4354_, v___x_4429_);
                if v___x_4430_ == 0 {
                    lean_dec(v_x_4354_);
                    v___x_4431_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1,
                    );
                    v___x_4432_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4431_, v_a_4355_, v_a_4356_);
                    return v___x_4432_;
                } else {
                    v___x_4433_ = lean_unsigned_to_nat(0);
                    v___x_4434_ = l_Lean_Syntax_getArg(v_x_4354_, v___x_4433_);
                    v___x_4435_ = l_Lean_Syntax_isNone(v___x_4434_);
                    if v___x_4435_ == 0 {
                        v___x_4436_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_4434_);
                        v___x_4437_ = l_Lean_Syntax_matchesNull(v___x_4434_, v___x_4436_);
                        if v___x_4437_ == 0 {
                            lean_dec(v___x_4434_);
                            lean_dec(v_x_4354_);
                            v___x_4438_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once
                                ),
                                _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1,
                            );
                            v___x_4439_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4438_, v_a_4355_, v_a_4356_);
                            return v___x_4439_;
                        } else {
                            v_doc_4440_ = l_Lean_Syntax_getArg(v___x_4434_, v___x_4433_);
                            lean_dec(v___x_4434_);
                            v___x_4441_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8;
                            lean_inc(v_doc_4440_);
                            v___x_4442_ = l_Lean_Syntax_isOfKind(v_doc_4440_, v___x_4441_);
                            if v___x_4442_ == 0 {
                                lean_dec(v_doc_4440_);
                                lean_dec(v_x_4354_);
                                v___x_4443_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once), _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
                                v___x_4444_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4443_, v_a_4355_, v_a_4356_);
                                return v___x_4444_;
                            } else {
                                v___x_4445_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4445_, 0, v_doc_4440_);
                                v_doc_4395_ = v___x_4445_;
                                v___y_4396_ = v_a_4355_;
                                v___y_4397_ = v_a_4356_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4434_);
                        v___x_4446_ = lean_box(0);
                        v_doc_4395_ = v___x_4446_;
                        v___y_4396_ = v_a_4355_;
                        v___y_4397_ = v_a_4356_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4363_ = lean_st_ref_take(v___y_4361_);
                v_env_4364_ = lean_ctor_get(v___x_4363_, 0);
                v_messages_4365_ = lean_ctor_get(v___x_4363_, 1);
                v_scopes_4366_ = lean_ctor_get(v___x_4363_, 2);
                v_usedQuotCtxts_4367_ = lean_ctor_get(v___x_4363_, 3);
                v_nextMacroScope_4368_ = lean_ctor_get(v___x_4363_, 4);
                v_maxRecDepth_4369_ = lean_ctor_get(v___x_4363_, 5);
                v_ngen_4370_ = lean_ctor_get(v___x_4363_, 6);
                v_auxDeclNGen_4371_ = lean_ctor_get(v___x_4363_, 7);
                v_infoState_4372_ = lean_ctor_get(v___x_4363_, 8);
                v_traceState_4373_ = lean_ctor_get(v___x_4363_, 9);
                v_snapshotTasks_4374_ = lean_ctor_get(v___x_4363_, 10);
                v_isSharedCheck_4393_ = (!lean_is_exclusive(v___x_4363_)) as u8;
                if v_isSharedCheck_4393_ == 0 {
                    v___x_4376_ = v___x_4363_;
                    v_isShared_4377_ = v_isSharedCheck_4393_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4374_);
                    lean_inc(v_traceState_4373_);
                    lean_inc(v_infoState_4372_);
                    lean_inc(v_auxDeclNGen_4371_);
                    lean_inc(v_ngen_4370_);
                    lean_inc(v_maxRecDepth_4369_);
                    lean_inc(v_nextMacroScope_4368_);
                    lean_inc(v_usedQuotCtxts_4367_);
                    lean_inc(v_scopes_4366_);
                    lean_inc(v_messages_4365_);
                    lean_inc(v_env_4364_);
                    lean_dec(v___x_4363_);
                    v___x_4376_ = lean_box(0);
                    v_isShared_4377_ = v_isSharedCheck_4393_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4378_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
                v_toEnvExtension_4379_ = lean_ctor_get(v___x_4378_, 0);
                v_asyncMode_4380_ = lean_ctor_get(v_toEnvExtension_4379_, 2);
                v___x_4381_ = l_Lean_TSyntax_getId(v___y_4359_);
                lean_dec(v___y_4359_);
                v___x_4382_ = l_Lean_TSyntax_getString(v___y_4360_);
                lean_dec(v___y_4360_);
                v___x_4383_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4383_, 0, v___x_4382_);
                lean_ctor_set(v___x_4383_, 1, v_a_4362_);
                v___x_4384_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4384_, 0, v___x_4381_);
                lean_ctor_set(v___x_4384_, 1, v___x_4383_);
                v___x_4385_ = lean_box(0);
                v___x_4386_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4378_,
                    v_env_4364_,
                    v___x_4384_,
                    v_asyncMode_4380_,
                    v___x_4385_,
                );
                if v_isShared_4377_ == 0 {
                    lean_ctor_set(v___x_4376_, 0, v___x_4386_);
                    v___x_4388_ = v___x_4376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4386_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 1, v_messages_4365_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 2, v_scopes_4366_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 3, v_usedQuotCtxts_4367_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 4, v_nextMacroScope_4368_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 5, v_maxRecDepth_4369_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 6, v_ngen_4370_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 7, v_auxDeclNGen_4371_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 8, v_infoState_4372_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 9, v_traceState_4373_);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 10, v_snapshotTasks_4374_);
                    v___x_4388_ = v_reuseFailAlloc_4392_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4389_ = lean_st_ref_set(v___y_4361_, v___x_4388_);
                v___x_4390_ = lean_box(0);
                v___x_4391_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4391_, 0, v___x_4390_);
                return v___x_4391_;
            }
            4 => {
                v___x_4398_ = lean_unsigned_to_nat(2);
                v_tag_4399_ = l_Lean_Syntax_getArg(v_x_4354_, v___x_4398_);
                v___x_4400_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10;
                lean_inc(v_tag_4399_);
                v___x_4401_ = l_Lean_Syntax_isOfKind(v_tag_4399_, v___x_4400_);
                if v___x_4401_ == 0 {
                    lean_dec(v_tag_4399_);
                    lean_dec(v_doc_4395_);
                    lean_dec(v_x_4354_);
                    v___x_4402_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1,
                    );
                    v___x_4403_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4402_, v___y_4396_, v___y_4397_);
                    return v___x_4403_;
                } else {
                    v___x_4404_ = lean_unsigned_to_nat(3);
                    v_user_4405_ = l_Lean_Syntax_getArg(v_x_4354_, v___x_4404_);
                    lean_dec(v_x_4354_);
                    v___x_4406_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3;
                    lean_inc(v_user_4405_);
                    v___x_4407_ = l_Lean_Syntax_isOfKind(v_user_4405_, v___x_4406_);
                    if v___x_4407_ == 0 {
                        lean_dec(v_user_4405_);
                        lean_dec(v_tag_4399_);
                        lean_dec(v_doc_4395_);
                        v___x_4408_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1,
                        );
                        v___x_4409_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_4408_, v___y_4396_, v___y_4397_);
                        return v___x_4409_;
                    } else {
                        if lean_obj_tag(v_doc_4395_) == 0 {
                            v___x_4410_ = lean_box(0);
                            v___y_4359_ = v_tag_4399_;
                            v___y_4360_ = v_user_4405_;
                            v___y_4361_ = v___y_4397_;
                            v_a_4362_ = v___x_4410_;
                            state = 1;
                            continue;
                        } else {
                            v_val_4411_ = lean_ctor_get(v_doc_4395_, 0);
                            v_isSharedCheck_4428_ = (!lean_is_exclusive(v_doc_4395_)) as u8;
                            if v_isSharedCheck_4428_ == 0 {
                                v___x_4413_ = v_doc_4395_;
                                v_isShared_4414_ = v_isSharedCheck_4428_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_val_4411_);
                                lean_dec(v_doc_4395_);
                                v___x_4413_ = lean_box(0);
                                v_isShared_4414_ = v_isSharedCheck_4428_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                v___x_4415_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_4411_, v___y_4396_, v___y_4397_);
                if lean_obj_tag(v___x_4415_) == 0 {
                    v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
                    lean_inc(v_a_4416_);
                    lean_dec_ref_known(v___x_4415_, 1);
                    if v_isShared_4414_ == 0 {
                        lean_ctor_set(v___x_4413_, 0, v_a_4416_);
                        v___x_4418_ = v___x_4413_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4416_);
                        v___x_4418_ = v_reuseFailAlloc_4419_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4413_);
                    lean_dec(v_user_4405_);
                    lean_dec(v_tag_4399_);
                    v_a_4420_ = lean_ctor_get(v___x_4415_, 0);
                    v_isSharedCheck_4427_ = (!lean_is_exclusive(v___x_4415_)) as u8;
                    if v_isSharedCheck_4427_ == 0 {
                        v___x_4422_ = v___x_4415_;
                        v_isShared_4423_ = v_isSharedCheck_4427_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4420_);
                        lean_dec(v___x_4415_);
                        v___x_4422_ = lean_box(0);
                        v_isShared_4423_ = v_isSharedCheck_4427_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___y_4359_ = v_tag_4399_;
                v___y_4360_ = v_user_4405_;
                v___y_4361_ = v___y_4397_;
                v_a_4362_ = v___x_4418_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_4423_ == 0 {
                    v___x_4425_ = v___x_4422_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
                    v___x_4425_ = v_reuseFailAlloc_4426_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(
    mut v_x_4447_: *mut LeanObject,
    mut v_a_4448_: *mut LeanObject,
    mut v_a_4449_: *mut LeanObject,
    mut v_a_4450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4451_: *mut LeanObject = core::ptr::null_mut();
    v_res_4451_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_4447_, v_a_4448_, v_a_4449_);
    lean_dec(v_a_4449_);
    lean_dec_ref(v_a_4448_);
    return v_res_4451_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1()
-> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4461_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5;
    v___x_4462_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1;
    v___x_4463_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4464_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4460_,
        v___x_4461_,
        v___x_4462_,
        v___x_4463_,
    );
    return v___x_4464_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(
    mut v_a_4465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4466_: *mut LeanObject = core::ptr::null_mut();
    v_res_4466_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
    return v_res_4466_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3()
-> *mut LeanObject {
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    v___x_4493_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1;
    v___x_4494_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6;
    v___x_4495_ = l_Lean_addBuiltinDeclarationRanges(v___x_4493_, v___x_4494_);
    return v___x_4495_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(
    mut v_a_4496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4497_: *mut LeanObject = core::ptr::null_mut();
    v_res_4497_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
    return v_res_4497_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(
    mut v___x_4498_: *mut LeanObject,
    mut v_x_4499_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4499_) == 0 {
        let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
        v___x_4500_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4500_, 0, v___x_4498_);
        return v___x_4500_;
    } else {
        lean_dec_ref(v___x_4498_);
        lean_inc_ref(v_x_4499_);
        return v_x_4499_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(
    mut v___x_4501_: *mut LeanObject,
    mut v_x_4502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4503_: *mut LeanObject = core::ptr::null_mut();
    v_res_4503_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_4501_, v_x_4502_);
    lean_dec(v_x_4502_);
    return v_res_4503_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(
    mut v___x_4504_: *mut LeanObject,
    mut v_k_4505_: *mut LeanObject,
    mut v_t_4506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4514_: u8 = 0;
    let mut v___x_4515_: u8 = 0;
    let mut v_impl_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v_size_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_unused_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_unused_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v_k_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4628_: u8 = 0;
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4639_: u8 = 0;
    let mut v_unused_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4661_: u8 = 0;
    let mut v_unused_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4667_: u8 = 0;
    let mut v_unused_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: u8 = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v_size_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4703_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut v_unused_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4738_: u8 = 0;
    let mut v_unused_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut v_unused_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v_k_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4783_: u8 = 0;
    let mut v_unused_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4791_: u8 = 0;
    let mut v_k_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4798_: u8 = 0;
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_unused_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4813_: u8 = 0;
    let mut v_unused_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut v_unused_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4837_: u8 = 0;
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_4506_) == 0 {
                    v_size_4507_ = lean_ctor_get(v_t_4506_, 0);
                    v_k_4508_ = lean_ctor_get(v_t_4506_, 1);
                    v_v_4509_ = lean_ctor_get(v_t_4506_, 2);
                    v_l_4510_ = lean_ctor_get(v_t_4506_, 3);
                    v_r_4511_ = lean_ctor_get(v_t_4506_, 4);
                    v_isSharedCheck_4837_ = (!lean_is_exclusive(v_t_4506_)) as u8;
                    if v_isSharedCheck_4837_ == 0 {
                        v___x_4513_ = v_t_4506_;
                        v_isShared_4514_ = v_isSharedCheck_4837_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_4511_);
                        lean_inc(v_l_4510_);
                        lean_inc(v_v_4509_);
                        lean_inc(v_k_4508_);
                        lean_inc(v_size_4507_);
                        lean_dec(v_t_4506_);
                        v___x_4513_ = lean_box(0);
                        v_isShared_4514_ = v_isSharedCheck_4837_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4838_ = lean_box(0);
                    v___x_4839_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_4504_, v___x_4838_);
                    if lean_obj_tag(v___x_4839_) == 0 {
                        lean_dec(v_k_4505_);
                        return v_t_4506_;
                    } else {
                        v_val_4840_ = lean_ctor_get(v___x_4839_, 0);
                        lean_inc(v_val_4840_);
                        lean_dec_ref_known(v___x_4839_, 1);
                        v___x_4841_ = lean_unsigned_to_nat(1);
                        v___x_4842_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v___x_4842_, 0, v___x_4841_);
                        lean_ctor_set(v___x_4842_, 1, v_k_4505_);
                        lean_ctor_set(v___x_4842_, 2, v_val_4840_);
                        lean_ctor_set(v___x_4842_, 3, v_t_4506_);
                        lean_ctor_set(v___x_4842_, 4, v_t_4506_);
                        return v___x_4842_;
                    }
                }
            }
            1 => {
                v___x_4515_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4505_, v_k_4508_);
                match v___x_4515_ {
                    0 => {
                        lean_del_object(v___x_4513_);
                        lean_dec(v_size_4507_);
                        v_impl_4516_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_4504_, v_k_4505_, v_l_4510_);
                        v___x_4517_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_4508_,
                            v_v_4509_,
                            v_impl_4516_,
                            v_r_4511_,
                        );
                        return v___x_4517_;
                    }
                    1 => {
                        lean_dec(v_k_4508_);
                        v___x_4518_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4518_, 0, v_v_4509_);
                        v___x_4519_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_4504_, v___x_4518_);
                        lean_dec_ref_known(v___x_4518_, 1);
                        if lean_obj_tag(v___x_4519_) == 0 {
                            lean_del_object(v___x_4513_);
                            lean_dec(v_size_4507_);
                            lean_dec(v_k_4505_);
                            if lean_obj_tag(v_l_4510_) == 0 {
                                if lean_obj_tag(v_r_4511_) == 0 {
                                    v_size_4520_ = lean_ctor_get(v_l_4510_, 0);
                                    v_k_4521_ = lean_ctor_get(v_l_4510_, 1);
                                    v_v_4522_ = lean_ctor_get(v_l_4510_, 2);
                                    v_l_4523_ = lean_ctor_get(v_l_4510_, 3);
                                    v_r_4524_ = lean_ctor_get(v_l_4510_, 4);
                                    lean_inc(v_r_4524_);
                                    v_size_4525_ = lean_ctor_get(v_r_4511_, 0);
                                    v_k_4526_ = lean_ctor_get(v_r_4511_, 1);
                                    v_v_4527_ = lean_ctor_get(v_r_4511_, 2);
                                    v_l_4528_ = lean_ctor_get(v_r_4511_, 3);
                                    lean_inc(v_l_4528_);
                                    v_r_4529_ = lean_ctor_get(v_r_4511_, 4);
                                    v___x_4530_ = lean_unsigned_to_nat(1);
                                    v___x_4531_ = lean_nat_dec_lt(v_size_4520_, v_size_4525_);
                                    if v___x_4531_ == 0 {
                                        lean_inc(v_l_4523_);
                                        lean_inc(v_v_4522_);
                                        lean_inc(v_k_4521_);
                                        v_isSharedCheck_4667_ =
                                            (!lean_is_exclusive(v_l_4510_)) as u8;
                                        if v_isSharedCheck_4667_ == 0 {
                                            v_unused_4668_ = lean_ctor_get(v_l_4510_, 4);
                                            lean_dec(v_unused_4668_);
                                            v_unused_4669_ = lean_ctor_get(v_l_4510_, 3);
                                            lean_dec(v_unused_4669_);
                                            v_unused_4670_ = lean_ctor_get(v_l_4510_, 2);
                                            lean_dec(v_unused_4670_);
                                            v_unused_4671_ = lean_ctor_get(v_l_4510_, 1);
                                            lean_dec(v_unused_4671_);
                                            v_unused_4672_ = lean_ctor_get(v_l_4510_, 0);
                                            lean_dec(v_unused_4672_);
                                            v___x_4533_ = v_l_4510_;
                                            v_isShared_4534_ = v_isSharedCheck_4667_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_dec(v_l_4510_);
                                            v___x_4533_ = lean_box(0);
                                            v_isShared_4534_ = v_isSharedCheck_4667_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_inc(v_r_4529_);
                                        lean_inc(v_v_4527_);
                                        lean_inc(v_k_4526_);
                                        v_isSharedCheck_4825_ =
                                            (!lean_is_exclusive(v_r_4511_)) as u8;
                                        if v_isSharedCheck_4825_ == 0 {
                                            v_unused_4826_ = lean_ctor_get(v_r_4511_, 4);
                                            lean_dec(v_unused_4826_);
                                            v_unused_4827_ = lean_ctor_get(v_r_4511_, 3);
                                            lean_dec(v_unused_4827_);
                                            v_unused_4828_ = lean_ctor_get(v_r_4511_, 2);
                                            lean_dec(v_unused_4828_);
                                            v_unused_4829_ = lean_ctor_get(v_r_4511_, 1);
                                            lean_dec(v_unused_4829_);
                                            v_unused_4830_ = lean_ctor_get(v_r_4511_, 0);
                                            lean_dec(v_unused_4830_);
                                            v___x_4674_ = v_r_4511_;
                                            v_isShared_4675_ = v_isSharedCheck_4825_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_dec(v_r_4511_);
                                            v___x_4674_ = lean_box(0);
                                            v_isShared_4675_ = v_isSharedCheck_4825_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v_l_4510_;
                                }
                            } else {
                                return v_r_4511_;
                            }
                        } else {
                            v_val_4831_ = lean_ctor_get(v___x_4519_, 0);
                            lean_inc(v_val_4831_);
                            lean_dec_ref_known(v___x_4519_, 1);
                            if v_isShared_4514_ == 0 {
                                lean_ctor_set(v___x_4513_, 2, v_val_4831_);
                                lean_ctor_set(v___x_4513_, 1, v_k_4505_);
                                v___x_4833_ = v___x_4513_;
                                state = 47;
                                continue;
                            } else {
                                v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_size_4507_);
                                lean_ctor_set(v_reuseFailAlloc_4834_, 1, v_k_4505_);
                                lean_ctor_set(v_reuseFailAlloc_4834_, 2, v_val_4831_);
                                lean_ctor_set(v_reuseFailAlloc_4834_, 3, v_l_4510_);
                                lean_ctor_set(v_reuseFailAlloc_4834_, 4, v_r_4511_);
                                v___x_4833_ = v_reuseFailAlloc_4834_;
                                state = 47;
                                continue;
                            }
                        }
                    }
                    _ => {
                        lean_del_object(v___x_4513_);
                        lean_dec(v_size_4507_);
                        v_impl_4835_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_4504_, v_k_4505_, v_r_4511_);
                        v___x_4836_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_4508_,
                            v_v_4509_,
                            v_l_4510_,
                            v_impl_4835_,
                        );
                        return v___x_4836_;
                    }
                }
            }
            2 => {
                v___x_4535_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_4521_, v_v_4522_, v_l_4523_, v_r_4524_,
                );
                v_tree_4536_ = lean_ctor_get(v___x_4535_, 2);
                lean_inc(v_tree_4536_);
                if lean_obj_tag(v_tree_4536_) == 0 {
                    v_k_4537_ = lean_ctor_get(v___x_4535_, 0);
                    lean_inc(v_k_4537_);
                    v_v_4538_ = lean_ctor_get(v___x_4535_, 1);
                    lean_inc(v_v_4538_);
                    lean_dec_ref(v___x_4535_);
                    v_size_4539_ = lean_ctor_get(v_tree_4536_, 0);
                    v___x_4540_ = lean_unsigned_to_nat(3);
                    v___x_4541_ = lean_nat_mul(v___x_4540_, v_size_4539_);
                    v___x_4542_ = lean_nat_dec_lt(v___x_4541_, v_size_4525_);
                    lean_dec(v___x_4541_);
                    if v___x_4542_ == 0 {
                        lean_dec(v_l_4528_);
                        v___x_4543_ = lean_nat_add(v___x_4530_, v_size_4539_);
                        v___x_4544_ = lean_nat_add(v___x_4543_, v_size_4525_);
                        lean_dec(v___x_4543_);
                        if v_isShared_4534_ == 0 {
                            lean_ctor_set(v___x_4533_, 4, v_r_4511_);
                            lean_ctor_set(v___x_4533_, 3, v_tree_4536_);
                            lean_ctor_set(v___x_4533_, 2, v_v_4538_);
                            lean_ctor_set(v___x_4533_, 1, v_k_4537_);
                            lean_ctor_set(v___x_4533_, 0, v___x_4544_);
                            v___x_4546_ = v___x_4533_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4544_);
                            lean_ctor_set(v_reuseFailAlloc_4547_, 1, v_k_4537_);
                            lean_ctor_set(v_reuseFailAlloc_4547_, 2, v_v_4538_);
                            lean_ctor_set(v_reuseFailAlloc_4547_, 3, v_tree_4536_);
                            lean_ctor_set(v_reuseFailAlloc_4547_, 4, v_r_4511_);
                            v___x_4546_ = v_reuseFailAlloc_4547_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_inc(v_r_4529_);
                        lean_inc(v_v_4527_);
                        lean_inc(v_k_4526_);
                        lean_inc(v_size_4525_);
                        v_isSharedCheck_4602_ = (!lean_is_exclusive(v_r_4511_)) as u8;
                        if v_isSharedCheck_4602_ == 0 {
                            v_unused_4603_ = lean_ctor_get(v_r_4511_, 4);
                            lean_dec(v_unused_4603_);
                            v_unused_4604_ = lean_ctor_get(v_r_4511_, 3);
                            lean_dec(v_unused_4604_);
                            v_unused_4605_ = lean_ctor_get(v_r_4511_, 2);
                            lean_dec(v_unused_4605_);
                            v_unused_4606_ = lean_ctor_get(v_r_4511_, 1);
                            lean_dec(v_unused_4606_);
                            v_unused_4607_ = lean_ctor_get(v_r_4511_, 0);
                            lean_dec(v_unused_4607_);
                            v___x_4549_ = v_r_4511_;
                            v_isShared_4550_ = v_isSharedCheck_4602_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_r_4511_);
                            v___x_4549_ = lean_box(0);
                            v_isShared_4550_ = v_isSharedCheck_4602_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_r_4529_);
                    lean_inc(v_v_4527_);
                    lean_inc(v_k_4526_);
                    lean_inc(v_size_4525_);
                    v_isSharedCheck_4661_ = (!lean_is_exclusive(v_r_4511_)) as u8;
                    if v_isSharedCheck_4661_ == 0 {
                        v_unused_4662_ = lean_ctor_get(v_r_4511_, 4);
                        lean_dec(v_unused_4662_);
                        v_unused_4663_ = lean_ctor_get(v_r_4511_, 3);
                        lean_dec(v_unused_4663_);
                        v_unused_4664_ = lean_ctor_get(v_r_4511_, 2);
                        lean_dec(v_unused_4664_);
                        v_unused_4665_ = lean_ctor_get(v_r_4511_, 1);
                        lean_dec(v_unused_4665_);
                        v_unused_4666_ = lean_ctor_get(v_r_4511_, 0);
                        lean_dec(v_unused_4666_);
                        v___x_4609_ = v_r_4511_;
                        v_isShared_4610_ = v_isSharedCheck_4661_;
                        state = 13;
                        continue;
                    } else {
                        lean_dec(v_r_4511_);
                        v___x_4609_ = lean_box(0);
                        v_isShared_4610_ = v_isSharedCheck_4661_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4546_;
            }
            4 => {
                v_size_4551_ = lean_ctor_get(v_l_4528_, 0);
                v_k_4552_ = lean_ctor_get(v_l_4528_, 1);
                v_v_4553_ = lean_ctor_get(v_l_4528_, 2);
                v_l_4554_ = lean_ctor_get(v_l_4528_, 3);
                v_r_4555_ = lean_ctor_get(v_l_4528_, 4);
                v_size_4556_ = lean_ctor_get(v_r_4529_, 0);
                v___x_4557_ = lean_unsigned_to_nat(2);
                v___x_4558_ = lean_nat_mul(v___x_4557_, v_size_4556_);
                v___x_4559_ = lean_nat_dec_lt(v_size_4551_, v___x_4558_);
                lean_dec(v___x_4558_);
                if v___x_4559_ == 0 {
                    lean_inc(v_r_4555_);
                    lean_inc(v_l_4554_);
                    lean_inc(v_v_4553_);
                    lean_inc(v_k_4552_);
                    v_isSharedCheck_4587_ = (!lean_is_exclusive(v_l_4528_)) as u8;
                    if v_isSharedCheck_4587_ == 0 {
                        v_unused_4588_ = lean_ctor_get(v_l_4528_, 4);
                        lean_dec(v_unused_4588_);
                        v_unused_4589_ = lean_ctor_get(v_l_4528_, 3);
                        lean_dec(v_unused_4589_);
                        v_unused_4590_ = lean_ctor_get(v_l_4528_, 2);
                        lean_dec(v_unused_4590_);
                        v_unused_4591_ = lean_ctor_get(v_l_4528_, 1);
                        lean_dec(v_unused_4591_);
                        v_unused_4592_ = lean_ctor_get(v_l_4528_, 0);
                        lean_dec(v_unused_4592_);
                        v___x_4561_ = v_l_4528_;
                        v_isShared_4562_ = v_isSharedCheck_4587_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_l_4528_);
                        v___x_4561_ = lean_box(0);
                        v_isShared_4562_ = v_isSharedCheck_4587_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_4593_ = lean_nat_add(v___x_4530_, v_size_4539_);
                    v___x_4594_ = lean_nat_add(v___x_4593_, v_size_4525_);
                    lean_dec(v_size_4525_);
                    v___x_4595_ = lean_nat_add(v___x_4593_, v_size_4551_);
                    lean_dec(v___x_4593_);
                    if v_isShared_4550_ == 0 {
                        lean_ctor_set(v___x_4549_, 4, v_l_4528_);
                        lean_ctor_set(v___x_4549_, 3, v_tree_4536_);
                        lean_ctor_set(v___x_4549_, 2, v_v_4538_);
                        lean_ctor_set(v___x_4549_, 1, v_k_4537_);
                        lean_ctor_set(v___x_4549_, 0, v___x_4595_);
                        v___x_4597_ = v___x_4549_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4595_);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_k_4537_);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 2, v_v_4538_);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 3, v_tree_4536_);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 4, v_l_4528_);
                        v___x_4597_ = v_reuseFailAlloc_4601_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4563_ = lean_nat_add(v___x_4530_, v_size_4539_);
                v___x_4564_ = lean_nat_add(v___x_4563_, v_size_4525_);
                lean_dec(v_size_4525_);
                if lean_obj_tag(v_l_4554_) == 0 {
                    v_size_4585_ = lean_ctor_get(v_l_4554_, 0);
                    lean_inc(v_size_4585_);
                    v___y_4577_ = v_size_4585_;
                    state = 9;
                    continue;
                } else {
                    v___x_4586_ = lean_unsigned_to_nat(0);
                    v___y_4577_ = v___x_4586_;
                    state = 9;
                    continue;
                }
            }
            6 => {
                v___x_4569_ = lean_nat_add(v___y_4566_, v___y_4568_);
                lean_dec(v___y_4568_);
                lean_dec(v___y_4566_);
                if v_isShared_4562_ == 0 {
                    lean_ctor_set(v___x_4561_, 4, v_r_4529_);
                    lean_ctor_set(v___x_4561_, 3, v_r_4555_);
                    lean_ctor_set(v___x_4561_, 2, v_v_4527_);
                    lean_ctor_set(v___x_4561_, 1, v_k_4526_);
                    lean_ctor_set(v___x_4561_, 0, v___x_4569_);
                    v___x_4571_ = v___x_4561_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4569_);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_k_4526_);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 2, v_v_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 3, v_r_4555_);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 4, v_r_4529_);
                    v___x_4571_ = v_reuseFailAlloc_4575_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4550_ == 0 {
                    lean_ctor_set(v___x_4549_, 4, v___x_4571_);
                    lean_ctor_set(v___x_4549_, 3, v___y_4567_);
                    lean_ctor_set(v___x_4549_, 2, v_v_4553_);
                    lean_ctor_set(v___x_4549_, 1, v_k_4552_);
                    lean_ctor_set(v___x_4549_, 0, v___x_4564_);
                    v___x_4573_ = v___x_4549_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4564_);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_k_4552_);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 2, v_v_4553_);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 3, v___y_4567_);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 4, v___x_4571_);
                    v___x_4573_ = v_reuseFailAlloc_4574_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4573_;
            }
            9 => {
                v___x_4578_ = lean_nat_add(v___x_4563_, v___y_4577_);
                lean_dec(v___y_4577_);
                lean_dec(v___x_4563_);
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 4, v_l_4554_);
                    lean_ctor_set(v___x_4533_, 3, v_tree_4536_);
                    lean_ctor_set(v___x_4533_, 2, v_v_4538_);
                    lean_ctor_set(v___x_4533_, 1, v_k_4537_);
                    lean_ctor_set(v___x_4533_, 0, v___x_4578_);
                    v___x_4580_ = v___x_4533_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4578_);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 1, v_k_4537_);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 2, v_v_4538_);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 3, v_tree_4536_);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 4, v_l_4554_);
                    v___x_4580_ = v_reuseFailAlloc_4584_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4581_ = lean_nat_add(v___x_4530_, v_size_4556_);
                if lean_obj_tag(v_r_4555_) == 0 {
                    v_size_4582_ = lean_ctor_get(v_r_4555_, 0);
                    lean_inc(v_size_4582_);
                    v___y_4566_ = v___x_4581_;
                    v___y_4567_ = v___x_4580_;
                    v___y_4568_ = v_size_4582_;
                    state = 6;
                    continue;
                } else {
                    v___x_4583_ = lean_unsigned_to_nat(0);
                    v___y_4566_ = v___x_4581_;
                    v___y_4567_ = v___x_4580_;
                    v___y_4568_ = v___x_4583_;
                    state = 6;
                    continue;
                }
            }
            11 => {
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 4, v_r_4529_);
                    lean_ctor_set(v___x_4533_, 3, v___x_4597_);
                    lean_ctor_set(v___x_4533_, 2, v_v_4527_);
                    lean_ctor_set(v___x_4533_, 1, v_k_4526_);
                    lean_ctor_set(v___x_4533_, 0, v___x_4594_);
                    v___x_4599_ = v___x_4533_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4594_);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_k_4526_);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_v_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 3, v___x_4597_);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 4, v_r_4529_);
                    v___x_4599_ = v_reuseFailAlloc_4600_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4599_;
            }
            13 => {
                if lean_obj_tag(v_l_4528_) == 0 {
                    if lean_obj_tag(v_r_4529_) == 0 {
                        v_k_4611_ = lean_ctor_get(v___x_4535_, 0);
                        lean_inc(v_k_4611_);
                        v_v_4612_ = lean_ctor_get(v___x_4535_, 1);
                        lean_inc(v_v_4612_);
                        lean_dec_ref(v___x_4535_);
                        v_size_4613_ = lean_ctor_get(v_l_4528_, 0);
                        v___x_4614_ = lean_nat_add(v___x_4530_, v_size_4525_);
                        lean_dec(v_size_4525_);
                        v___x_4615_ = lean_nat_add(v___x_4530_, v_size_4613_);
                        if v_isShared_4610_ == 0 {
                            lean_ctor_set(v___x_4609_, 4, v_l_4528_);
                            lean_ctor_set(v___x_4609_, 3, v_tree_4536_);
                            lean_ctor_set(v___x_4609_, 2, v_v_4612_);
                            lean_ctor_set(v___x_4609_, 1, v_k_4611_);
                            lean_ctor_set(v___x_4609_, 0, v___x_4615_);
                            v___x_4617_ = v___x_4609_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4615_);
                            lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_k_4611_);
                            lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_v_4612_);
                            lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_tree_4536_);
                            lean_ctor_set(v_reuseFailAlloc_4621_, 4, v_l_4528_);
                            v___x_4617_ = v_reuseFailAlloc_4621_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_4525_);
                        v_k_4622_ = lean_ctor_get(v___x_4535_, 0);
                        lean_inc(v_k_4622_);
                        v_v_4623_ = lean_ctor_get(v___x_4535_, 1);
                        lean_inc(v_v_4623_);
                        lean_dec_ref(v___x_4535_);
                        v_k_4624_ = lean_ctor_get(v_l_4528_, 1);
                        v_v_4625_ = lean_ctor_get(v_l_4528_, 2);
                        v_isSharedCheck_4639_ = (!lean_is_exclusive(v_l_4528_)) as u8;
                        if v_isSharedCheck_4639_ == 0 {
                            v_unused_4640_ = lean_ctor_get(v_l_4528_, 4);
                            lean_dec(v_unused_4640_);
                            v_unused_4641_ = lean_ctor_get(v_l_4528_, 3);
                            lean_dec(v_unused_4641_);
                            v_unused_4642_ = lean_ctor_get(v_l_4528_, 0);
                            lean_dec(v_unused_4642_);
                            v___x_4627_ = v_l_4528_;
                            v_isShared_4628_ = v_isSharedCheck_4639_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_v_4625_);
                            lean_inc(v_k_4624_);
                            lean_dec(v_l_4528_);
                            v___x_4627_ = lean_box(0);
                            v_isShared_4628_ = v_isSharedCheck_4639_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_r_4529_) == 0 {
                        lean_dec(v_size_4525_);
                        v_k_4643_ = lean_ctor_get(v___x_4535_, 0);
                        lean_inc(v_k_4643_);
                        v_v_4644_ = lean_ctor_get(v___x_4535_, 1);
                        lean_inc(v_v_4644_);
                        lean_dec_ref(v___x_4535_);
                        v___x_4645_ = lean_unsigned_to_nat(3);
                        if v_isShared_4610_ == 0 {
                            lean_ctor_set(v___x_4609_, 4, v_l_4528_);
                            lean_ctor_set(v___x_4609_, 2, v_v_4644_);
                            lean_ctor_set(v___x_4609_, 1, v_k_4643_);
                            lean_ctor_set(v___x_4609_, 0, v___x_4530_);
                            v___x_4647_ = v___x_4609_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4530_);
                            lean_ctor_set(v_reuseFailAlloc_4651_, 1, v_k_4643_);
                            lean_ctor_set(v_reuseFailAlloc_4651_, 2, v_v_4644_);
                            lean_ctor_set(v_reuseFailAlloc_4651_, 3, v_l_4528_);
                            lean_ctor_set(v_reuseFailAlloc_4651_, 4, v_l_4528_);
                            v___x_4647_ = v_reuseFailAlloc_4651_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v_k_4652_ = lean_ctor_get(v___x_4535_, 0);
                        lean_inc(v_k_4652_);
                        v_v_4653_ = lean_ctor_get(v___x_4535_, 1);
                        lean_inc(v_v_4653_);
                        lean_dec_ref(v___x_4535_);
                        if v_isShared_4610_ == 0 {
                            lean_ctor_set(v___x_4609_, 3, v_r_4529_);
                            v___x_4655_ = v___x_4609_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_size_4525_);
                            lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_k_4526_);
                            lean_ctor_set(v_reuseFailAlloc_4660_, 2, v_v_4527_);
                            lean_ctor_set(v_reuseFailAlloc_4660_, 3, v_r_4529_);
                            lean_ctor_set(v_reuseFailAlloc_4660_, 4, v_r_4529_);
                            v___x_4655_ = v_reuseFailAlloc_4660_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 4, v_r_4529_);
                    lean_ctor_set(v___x_4533_, 3, v___x_4617_);
                    lean_ctor_set(v___x_4533_, 2, v_v_4527_);
                    lean_ctor_set(v___x_4533_, 1, v_k_4526_);
                    lean_ctor_set(v___x_4533_, 0, v___x_4614_);
                    v___x_4619_ = v___x_4533_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4614_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_k_4526_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 2, v_v_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 3, v___x_4617_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 4, v_r_4529_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4619_;
            }
            16 => {
                v___x_4629_ = lean_unsigned_to_nat(3);
                if v_isShared_4628_ == 0 {
                    lean_ctor_set(v___x_4627_, 4, v_r_4529_);
                    lean_ctor_set(v___x_4627_, 3, v_r_4529_);
                    lean_ctor_set(v___x_4627_, 2, v_v_4623_);
                    lean_ctor_set(v___x_4627_, 1, v_k_4622_);
                    lean_ctor_set(v___x_4627_, 0, v___x_4530_);
                    v___x_4631_ = v___x_4627_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_k_4622_);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 2, v_v_4623_);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 3, v_r_4529_);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 4, v_r_4529_);
                    v___x_4631_ = v_reuseFailAlloc_4638_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4610_ == 0 {
                    lean_ctor_set(v___x_4609_, 3, v_r_4529_);
                    lean_ctor_set(v___x_4609_, 0, v___x_4530_);
                    v___x_4633_ = v___x_4609_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4637_, 1, v_k_4526_);
                    lean_ctor_set(v_reuseFailAlloc_4637_, 2, v_v_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4637_, 3, v_r_4529_);
                    lean_ctor_set(v_reuseFailAlloc_4637_, 4, v_r_4529_);
                    v___x_4633_ = v_reuseFailAlloc_4637_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 4, v___x_4633_);
                    lean_ctor_set(v___x_4533_, 3, v___x_4631_);
                    lean_ctor_set(v___x_4533_, 2, v_v_4625_);
                    lean_ctor_set(v___x_4533_, 1, v_k_4624_);
                    lean_ctor_set(v___x_4533_, 0, v___x_4629_);
                    v___x_4635_ = v___x_4533_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4629_);
                    lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_k_4624_);
                    lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_v_4625_);
                    lean_ctor_set(v_reuseFailAlloc_4636_, 3, v___x_4631_);
                    lean_ctor_set(v_reuseFailAlloc_4636_, 4, v___x_4633_);
                    v___x_4635_ = v_reuseFailAlloc_4636_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4635_;
            }
            20 => {
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 4, v_r_4529_);
                    lean_ctor_set(v___x_4533_, 3, v___x_4647_);
                    lean_ctor_set(v___x_4533_, 2, v_v_4527_);
                    lean_ctor_set(v___x_4533_, 1, v_k_4526_);
                    lean_ctor_set(v___x_4533_, 0, v___x_4645_);
                    v___x_4649_ = v___x_4533_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4645_);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_k_4526_);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_v_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 3, v___x_4647_);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 4, v_r_4529_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4649_;
            }
            22 => {
                v___x_4656_ = lean_unsigned_to_nat(2);
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 4, v___x_4655_);
                    lean_ctor_set(v___x_4533_, 3, v_r_4529_);
                    lean_ctor_set(v___x_4533_, 2, v_v_4653_);
                    lean_ctor_set(v___x_4533_, 1, v_k_4652_);
                    lean_ctor_set(v___x_4533_, 0, v___x_4656_);
                    v___x_4658_ = v___x_4533_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4656_);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_k_4652_);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 2, v_v_4653_);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 3, v_r_4529_);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 4, v___x_4655_);
                    v___x_4658_ = v_reuseFailAlloc_4659_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4658_;
            }
            24 => {
                v___x_4676_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_4526_, v_v_4527_, v_l_4528_, v_r_4529_,
                );
                v_tree_4677_ = lean_ctor_get(v___x_4676_, 2);
                lean_inc(v_tree_4677_);
                if lean_obj_tag(v_tree_4677_) == 0 {
                    v_k_4678_ = lean_ctor_get(v___x_4676_, 0);
                    lean_inc(v_k_4678_);
                    v_v_4679_ = lean_ctor_get(v___x_4676_, 1);
                    lean_inc(v_v_4679_);
                    lean_dec_ref(v___x_4676_);
                    v_size_4680_ = lean_ctor_get(v_tree_4677_, 0);
                    v___x_4681_ = lean_unsigned_to_nat(3);
                    v___x_4682_ = lean_nat_mul(v___x_4681_, v_size_4680_);
                    v___x_4683_ = lean_nat_dec_lt(v___x_4682_, v_size_4520_);
                    lean_dec(v___x_4682_);
                    if v___x_4683_ == 0 {
                        lean_dec(v_r_4524_);
                        v___x_4684_ = lean_nat_add(v___x_4530_, v_size_4520_);
                        v___x_4685_ = lean_nat_add(v___x_4684_, v_size_4680_);
                        lean_dec(v___x_4684_);
                        if v_isShared_4675_ == 0 {
                            lean_ctor_set(v___x_4674_, 4, v_tree_4677_);
                            lean_ctor_set(v___x_4674_, 3, v_l_4510_);
                            lean_ctor_set(v___x_4674_, 2, v_v_4679_);
                            lean_ctor_set(v___x_4674_, 1, v_k_4678_);
                            lean_ctor_set(v___x_4674_, 0, v___x_4685_);
                            v___x_4687_ = v___x_4674_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
                            lean_ctor_set(v_reuseFailAlloc_4688_, 1, v_k_4678_);
                            lean_ctor_set(v_reuseFailAlloc_4688_, 2, v_v_4679_);
                            lean_ctor_set(v_reuseFailAlloc_4688_, 3, v_l_4510_);
                            lean_ctor_set(v_reuseFailAlloc_4688_, 4, v_tree_4677_);
                            v___x_4687_ = v_reuseFailAlloc_4688_;
                            state = 25;
                            continue;
                        }
                    } else {
                        lean_inc(v_l_4523_);
                        lean_inc(v_v_4522_);
                        lean_inc(v_k_4521_);
                        lean_inc(v_size_4520_);
                        v_isSharedCheck_4754_ = (!lean_is_exclusive(v_l_4510_)) as u8;
                        if v_isSharedCheck_4754_ == 0 {
                            v_unused_4755_ = lean_ctor_get(v_l_4510_, 4);
                            lean_dec(v_unused_4755_);
                            v_unused_4756_ = lean_ctor_get(v_l_4510_, 3);
                            lean_dec(v_unused_4756_);
                            v_unused_4757_ = lean_ctor_get(v_l_4510_, 2);
                            lean_dec(v_unused_4757_);
                            v_unused_4758_ = lean_ctor_get(v_l_4510_, 1);
                            lean_dec(v_unused_4758_);
                            v_unused_4759_ = lean_ctor_get(v_l_4510_, 0);
                            lean_dec(v_unused_4759_);
                            v___x_4690_ = v_l_4510_;
                            v_isShared_4691_ = v_isSharedCheck_4754_;
                            state = 26;
                            continue;
                        } else {
                            lean_dec(v_l_4510_);
                            v___x_4690_ = lean_box(0);
                            v_isShared_4691_ = v_isSharedCheck_4754_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_l_4523_) == 0 {
                        lean_inc_ref(v_l_4523_);
                        lean_inc(v_v_4522_);
                        lean_inc(v_k_4521_);
                        lean_inc(v_size_4520_);
                        v_isSharedCheck_4783_ = (!lean_is_exclusive(v_l_4510_)) as u8;
                        if v_isSharedCheck_4783_ == 0 {
                            v_unused_4784_ = lean_ctor_get(v_l_4510_, 4);
                            lean_dec(v_unused_4784_);
                            v_unused_4785_ = lean_ctor_get(v_l_4510_, 3);
                            lean_dec(v_unused_4785_);
                            v_unused_4786_ = lean_ctor_get(v_l_4510_, 2);
                            lean_dec(v_unused_4786_);
                            v_unused_4787_ = lean_ctor_get(v_l_4510_, 1);
                            lean_dec(v_unused_4787_);
                            v_unused_4788_ = lean_ctor_get(v_l_4510_, 0);
                            lean_dec(v_unused_4788_);
                            v___x_4761_ = v_l_4510_;
                            v_isShared_4762_ = v_isSharedCheck_4783_;
                            state = 36;
                            continue;
                        } else {
                            lean_dec(v_l_4510_);
                            v___x_4761_ = lean_box(0);
                            v_isShared_4762_ = v_isSharedCheck_4783_;
                            state = 36;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_r_4524_) == 0 {
                            lean_inc(v_l_4523_);
                            lean_inc(v_v_4522_);
                            lean_inc(v_k_4521_);
                            v_isSharedCheck_4813_ = (!lean_is_exclusive(v_l_4510_)) as u8;
                            if v_isSharedCheck_4813_ == 0 {
                                v_unused_4814_ = lean_ctor_get(v_l_4510_, 4);
                                lean_dec(v_unused_4814_);
                                v_unused_4815_ = lean_ctor_get(v_l_4510_, 3);
                                lean_dec(v_unused_4815_);
                                v_unused_4816_ = lean_ctor_get(v_l_4510_, 2);
                                lean_dec(v_unused_4816_);
                                v_unused_4817_ = lean_ctor_get(v_l_4510_, 1);
                                lean_dec(v_unused_4817_);
                                v_unused_4818_ = lean_ctor_get(v_l_4510_, 0);
                                lean_dec(v_unused_4818_);
                                v___x_4790_ = v_l_4510_;
                                v_isShared_4791_ = v_isSharedCheck_4813_;
                                state = 41;
                                continue;
                            } else {
                                lean_dec(v_l_4510_);
                                v___x_4790_ = lean_box(0);
                                v_isShared_4791_ = v_isSharedCheck_4813_;
                                state = 41;
                                continue;
                            }
                        } else {
                            v_k_4819_ = lean_ctor_get(v___x_4676_, 0);
                            lean_inc(v_k_4819_);
                            v_v_4820_ = lean_ctor_get(v___x_4676_, 1);
                            lean_inc(v_v_4820_);
                            lean_dec_ref(v___x_4676_);
                            v___x_4821_ = lean_unsigned_to_nat(2);
                            if v_isShared_4675_ == 0 {
                                lean_ctor_set(v___x_4674_, 4, v_r_4524_);
                                lean_ctor_set(v___x_4674_, 3, v_l_4510_);
                                lean_ctor_set(v___x_4674_, 2, v_v_4820_);
                                lean_ctor_set(v___x_4674_, 1, v_k_4819_);
                                lean_ctor_set(v___x_4674_, 0, v___x_4821_);
                                v___x_4823_ = v___x_4674_;
                                state = 46;
                                continue;
                            } else {
                                v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
                                lean_ctor_set(v_reuseFailAlloc_4824_, 1, v_k_4819_);
                                lean_ctor_set(v_reuseFailAlloc_4824_, 2, v_v_4820_);
                                lean_ctor_set(v_reuseFailAlloc_4824_, 3, v_l_4510_);
                                lean_ctor_set(v_reuseFailAlloc_4824_, 4, v_r_4524_);
                                v___x_4823_ = v_reuseFailAlloc_4824_;
                                state = 46;
                                continue;
                            }
                        }
                    }
                }
            }
            25 => {
                return v___x_4687_;
            }
            26 => {
                v_size_4692_ = lean_ctor_get(v_l_4523_, 0);
                v_size_4693_ = lean_ctor_get(v_r_4524_, 0);
                v_k_4694_ = lean_ctor_get(v_r_4524_, 1);
                v_v_4695_ = lean_ctor_get(v_r_4524_, 2);
                v_l_4696_ = lean_ctor_get(v_r_4524_, 3);
                v_r_4697_ = lean_ctor_get(v_r_4524_, 4);
                v___x_4698_ = lean_unsigned_to_nat(2);
                v___x_4699_ = lean_nat_mul(v___x_4698_, v_size_4692_);
                v___x_4700_ = lean_nat_dec_lt(v_size_4693_, v___x_4699_);
                lean_dec(v___x_4699_);
                if v___x_4700_ == 0 {
                    lean_inc(v_r_4697_);
                    lean_inc(v_l_4696_);
                    lean_inc(v_v_4695_);
                    lean_inc(v_k_4694_);
                    lean_del_object(v___x_4690_);
                    v_isSharedCheck_4738_ = (!lean_is_exclusive(v_r_4524_)) as u8;
                    if v_isSharedCheck_4738_ == 0 {
                        v_unused_4739_ = lean_ctor_get(v_r_4524_, 4);
                        lean_dec(v_unused_4739_);
                        v_unused_4740_ = lean_ctor_get(v_r_4524_, 3);
                        lean_dec(v_unused_4740_);
                        v_unused_4741_ = lean_ctor_get(v_r_4524_, 2);
                        lean_dec(v_unused_4741_);
                        v_unused_4742_ = lean_ctor_get(v_r_4524_, 1);
                        lean_dec(v_unused_4742_);
                        v_unused_4743_ = lean_ctor_get(v_r_4524_, 0);
                        lean_dec(v_unused_4743_);
                        v___x_4702_ = v_r_4524_;
                        v_isShared_4703_ = v_isSharedCheck_4738_;
                        state = 27;
                        continue;
                    } else {
                        lean_dec(v_r_4524_);
                        v___x_4702_ = lean_box(0);
                        v_isShared_4703_ = v_isSharedCheck_4738_;
                        state = 27;
                        continue;
                    }
                } else {
                    v___x_4744_ = lean_nat_add(v___x_4530_, v_size_4520_);
                    lean_dec(v_size_4520_);
                    v___x_4745_ = lean_nat_add(v___x_4744_, v_size_4680_);
                    lean_dec(v___x_4744_);
                    v___x_4746_ = lean_nat_add(v___x_4530_, v_size_4680_);
                    v___x_4747_ = lean_nat_add(v___x_4746_, v_size_4693_);
                    lean_dec(v___x_4746_);
                    if v_isShared_4675_ == 0 {
                        lean_ctor_set(v___x_4674_, 4, v_tree_4677_);
                        lean_ctor_set(v___x_4674_, 3, v_r_4524_);
                        lean_ctor_set(v___x_4674_, 2, v_v_4679_);
                        lean_ctor_set(v___x_4674_, 1, v_k_4678_);
                        lean_ctor_set(v___x_4674_, 0, v___x_4747_);
                        v___x_4749_ = v___x_4674_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4747_);
                        lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_k_4678_);
                        lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_v_4679_);
                        lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_r_4524_);
                        lean_ctor_set(v_reuseFailAlloc_4753_, 4, v_tree_4677_);
                        v___x_4749_ = v_reuseFailAlloc_4753_;
                        state = 34;
                        continue;
                    }
                }
            }
            27 => {
                v___x_4704_ = lean_nat_add(v___x_4530_, v_size_4520_);
                lean_dec(v_size_4520_);
                v___x_4705_ = lean_nat_add(v___x_4704_, v_size_4680_);
                lean_dec(v___x_4704_);
                v___x_4726_ = lean_nat_add(v___x_4530_, v_size_4692_);
                if lean_obj_tag(v_l_4696_) == 0 {
                    v_size_4736_ = lean_ctor_get(v_l_4696_, 0);
                    lean_inc(v_size_4736_);
                    v___y_4728_ = v_size_4736_;
                    state = 32;
                    continue;
                } else {
                    v___x_4737_ = lean_unsigned_to_nat(0);
                    v___y_4728_ = v___x_4737_;
                    state = 32;
                    continue;
                }
            }
            28 => {
                v___x_4710_ = lean_nat_add(v___y_4708_, v___y_4709_);
                lean_dec(v___y_4709_);
                lean_dec(v___y_4708_);
                lean_inc_ref(v_tree_4677_);
                if v_isShared_4703_ == 0 {
                    lean_ctor_set(v___x_4702_, 4, v_tree_4677_);
                    lean_ctor_set(v___x_4702_, 3, v_r_4697_);
                    lean_ctor_set(v___x_4702_, 2, v_v_4679_);
                    lean_ctor_set(v___x_4702_, 1, v_k_4678_);
                    lean_ctor_set(v___x_4702_, 0, v___x_4710_);
                    v___x_4712_ = v___x_4702_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4710_);
                    lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_k_4678_);
                    lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_v_4679_);
                    lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_r_4697_);
                    lean_ctor_set(v_reuseFailAlloc_4725_, 4, v_tree_4677_);
                    v___x_4712_ = v_reuseFailAlloc_4725_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v_isSharedCheck_4719_ = (!lean_is_exclusive(v_tree_4677_)) as u8;
                if v_isSharedCheck_4719_ == 0 {
                    v_unused_4720_ = lean_ctor_get(v_tree_4677_, 4);
                    lean_dec(v_unused_4720_);
                    v_unused_4721_ = lean_ctor_get(v_tree_4677_, 3);
                    lean_dec(v_unused_4721_);
                    v_unused_4722_ = lean_ctor_get(v_tree_4677_, 2);
                    lean_dec(v_unused_4722_);
                    v_unused_4723_ = lean_ctor_get(v_tree_4677_, 1);
                    lean_dec(v_unused_4723_);
                    v_unused_4724_ = lean_ctor_get(v_tree_4677_, 0);
                    lean_dec(v_unused_4724_);
                    v___x_4714_ = v_tree_4677_;
                    v_isShared_4715_ = v_isSharedCheck_4719_;
                    state = 30;
                    continue;
                } else {
                    lean_dec(v_tree_4677_);
                    v___x_4714_ = lean_box(0);
                    v_isShared_4715_ = v_isSharedCheck_4719_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_4715_ == 0 {
                    lean_ctor_set(v___x_4714_, 4, v___x_4712_);
                    lean_ctor_set(v___x_4714_, 3, v___y_4707_);
                    lean_ctor_set(v___x_4714_, 2, v_v_4695_);
                    lean_ctor_set(v___x_4714_, 1, v_k_4694_);
                    lean_ctor_set(v___x_4714_, 0, v___x_4705_);
                    v___x_4717_ = v___x_4714_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4705_);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_k_4694_);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 2, v_v_4695_);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 3, v___y_4707_);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 4, v___x_4712_);
                    v___x_4717_ = v_reuseFailAlloc_4718_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4717_;
            }
            32 => {
                v___x_4729_ = lean_nat_add(v___x_4726_, v___y_4728_);
                lean_dec(v___y_4728_);
                lean_dec(v___x_4726_);
                if v_isShared_4675_ == 0 {
                    lean_ctor_set(v___x_4674_, 4, v_l_4696_);
                    lean_ctor_set(v___x_4674_, 3, v_l_4523_);
                    lean_ctor_set(v___x_4674_, 2, v_v_4522_);
                    lean_ctor_set(v___x_4674_, 1, v_k_4521_);
                    lean_ctor_set(v___x_4674_, 0, v___x_4729_);
                    v___x_4731_ = v___x_4674_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4729_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_k_4521_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_v_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 3, v_l_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 4, v_l_4696_);
                    v___x_4731_ = v_reuseFailAlloc_4735_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_4732_ = lean_nat_add(v___x_4530_, v_size_4680_);
                if lean_obj_tag(v_r_4697_) == 0 {
                    v_size_4733_ = lean_ctor_get(v_r_4697_, 0);
                    lean_inc(v_size_4733_);
                    v___y_4707_ = v___x_4731_;
                    v___y_4708_ = v___x_4732_;
                    v___y_4709_ = v_size_4733_;
                    state = 28;
                    continue;
                } else {
                    v___x_4734_ = lean_unsigned_to_nat(0);
                    v___y_4707_ = v___x_4731_;
                    v___y_4708_ = v___x_4732_;
                    v___y_4709_ = v___x_4734_;
                    state = 28;
                    continue;
                }
            }
            34 => {
                if v_isShared_4691_ == 0 {
                    lean_ctor_set(v___x_4690_, 4, v___x_4749_);
                    lean_ctor_set(v___x_4690_, 0, v___x_4745_);
                    v___x_4751_ = v___x_4690_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4745_);
                    lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_k_4521_);
                    lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_v_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4752_, 3, v_l_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4752_, 4, v___x_4749_);
                    v___x_4751_ = v_reuseFailAlloc_4752_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4751_;
            }
            36 => {
                if lean_obj_tag(v_r_4524_) == 0 {
                    v_k_4763_ = lean_ctor_get(v___x_4676_, 0);
                    lean_inc(v_k_4763_);
                    v_v_4764_ = lean_ctor_get(v___x_4676_, 1);
                    lean_inc(v_v_4764_);
                    lean_dec_ref(v___x_4676_);
                    v_size_4765_ = lean_ctor_get(v_r_4524_, 0);
                    v___x_4766_ = lean_nat_add(v___x_4530_, v_size_4520_);
                    lean_dec(v_size_4520_);
                    v___x_4767_ = lean_nat_add(v___x_4530_, v_size_4765_);
                    if v_isShared_4675_ == 0 {
                        lean_ctor_set(v___x_4674_, 4, v_tree_4677_);
                        lean_ctor_set(v___x_4674_, 3, v_r_4524_);
                        lean_ctor_set(v___x_4674_, 2, v_v_4764_);
                        lean_ctor_set(v___x_4674_, 1, v_k_4763_);
                        lean_ctor_set(v___x_4674_, 0, v___x_4767_);
                        v___x_4769_ = v___x_4674_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4767_);
                        lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_k_4763_);
                        lean_ctor_set(v_reuseFailAlloc_4773_, 2, v_v_4764_);
                        lean_ctor_set(v_reuseFailAlloc_4773_, 3, v_r_4524_);
                        lean_ctor_set(v_reuseFailAlloc_4773_, 4, v_tree_4677_);
                        v___x_4769_ = v_reuseFailAlloc_4773_;
                        state = 37;
                        continue;
                    }
                } else {
                    lean_dec(v_size_4520_);
                    v_k_4774_ = lean_ctor_get(v___x_4676_, 0);
                    lean_inc(v_k_4774_);
                    v_v_4775_ = lean_ctor_get(v___x_4676_, 1);
                    lean_inc(v_v_4775_);
                    lean_dec_ref(v___x_4676_);
                    v___x_4776_ = lean_unsigned_to_nat(3);
                    if v_isShared_4675_ == 0 {
                        lean_ctor_set(v___x_4674_, 4, v_r_4524_);
                        lean_ctor_set(v___x_4674_, 3, v_r_4524_);
                        lean_ctor_set(v___x_4674_, 2, v_v_4775_);
                        lean_ctor_set(v___x_4674_, 1, v_k_4774_);
                        lean_ctor_set(v___x_4674_, 0, v___x_4530_);
                        v___x_4778_ = v___x_4674_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4530_);
                        lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_k_4774_);
                        lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_v_4775_);
                        lean_ctor_set(v_reuseFailAlloc_4782_, 3, v_r_4524_);
                        lean_ctor_set(v_reuseFailAlloc_4782_, 4, v_r_4524_);
                        v___x_4778_ = v_reuseFailAlloc_4782_;
                        state = 39;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_4762_ == 0 {
                    lean_ctor_set(v___x_4761_, 4, v___x_4769_);
                    lean_ctor_set(v___x_4761_, 0, v___x_4766_);
                    v___x_4771_ = v___x_4761_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4766_);
                    lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_k_4521_);
                    lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_v_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4772_, 3, v_l_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4772_, 4, v___x_4769_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4771_;
            }
            39 => {
                if v_isShared_4762_ == 0 {
                    lean_ctor_set(v___x_4761_, 4, v___x_4778_);
                    lean_ctor_set(v___x_4761_, 0, v___x_4776_);
                    v___x_4780_ = v___x_4761_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4776_);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 1, v_k_4521_);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 2, v_v_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 3, v_l_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 4, v___x_4778_);
                    v___x_4780_ = v_reuseFailAlloc_4781_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4780_;
            }
            41 => {
                v_k_4792_ = lean_ctor_get(v___x_4676_, 0);
                lean_inc(v_k_4792_);
                v_v_4793_ = lean_ctor_get(v___x_4676_, 1);
                lean_inc(v_v_4793_);
                lean_dec_ref(v___x_4676_);
                v_k_4794_ = lean_ctor_get(v_r_4524_, 1);
                v_v_4795_ = lean_ctor_get(v_r_4524_, 2);
                v_isSharedCheck_4809_ = (!lean_is_exclusive(v_r_4524_)) as u8;
                if v_isSharedCheck_4809_ == 0 {
                    v_unused_4810_ = lean_ctor_get(v_r_4524_, 4);
                    lean_dec(v_unused_4810_);
                    v_unused_4811_ = lean_ctor_get(v_r_4524_, 3);
                    lean_dec(v_unused_4811_);
                    v_unused_4812_ = lean_ctor_get(v_r_4524_, 0);
                    lean_dec(v_unused_4812_);
                    v___x_4797_ = v_r_4524_;
                    v_isShared_4798_ = v_isSharedCheck_4809_;
                    state = 42;
                    continue;
                } else {
                    lean_inc(v_v_4795_);
                    lean_inc(v_k_4794_);
                    lean_dec(v_r_4524_);
                    v___x_4797_ = lean_box(0);
                    v_isShared_4798_ = v_isSharedCheck_4809_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_4799_ = lean_unsigned_to_nat(3);
                if v_isShared_4798_ == 0 {
                    lean_ctor_set(v___x_4797_, 4, v_l_4523_);
                    lean_ctor_set(v___x_4797_, 3, v_l_4523_);
                    lean_ctor_set(v___x_4797_, 2, v_v_4522_);
                    lean_ctor_set(v___x_4797_, 1, v_k_4521_);
                    lean_ctor_set(v___x_4797_, 0, v___x_4530_);
                    v___x_4801_ = v___x_4797_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 1, v_k_4521_);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 2, v_v_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 3, v_l_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 4, v_l_4523_);
                    v___x_4801_ = v_reuseFailAlloc_4808_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_4675_ == 0 {
                    lean_ctor_set(v___x_4674_, 4, v_l_4523_);
                    lean_ctor_set(v___x_4674_, 3, v_l_4523_);
                    lean_ctor_set(v___x_4674_, 2, v_v_4793_);
                    lean_ctor_set(v___x_4674_, 1, v_k_4792_);
                    lean_ctor_set(v___x_4674_, 0, v___x_4530_);
                    v___x_4803_ = v___x_4674_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_k_4792_);
                    lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_v_4793_);
                    lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_l_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4807_, 4, v_l_4523_);
                    v___x_4803_ = v_reuseFailAlloc_4807_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_4791_ == 0 {
                    lean_ctor_set(v___x_4790_, 4, v___x_4803_);
                    lean_ctor_set(v___x_4790_, 3, v___x_4801_);
                    lean_ctor_set(v___x_4790_, 2, v_v_4795_);
                    lean_ctor_set(v___x_4790_, 1, v_k_4794_);
                    lean_ctor_set(v___x_4790_, 0, v___x_4799_);
                    v___x_4805_ = v___x_4790_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4799_);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_k_4794_);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_v_4795_);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 3, v___x_4801_);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 4, v___x_4803_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4805_;
            }
            46 => {
                return v___x_4823_;
            }
            47 => {
                return v___x_4833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4843_: *mut LeanObject,
    mut v_i_4844_: *mut LeanObject,
    mut v_k_4845_: *mut LeanObject,
) -> u8 {
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: u8 = 0;
    let mut v_k_x27_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4846_ = lean_array_get_size(v_keys_4843_);
                v___x_4847_ = lean_nat_dec_lt(v_i_4844_, v___x_4846_);
                if v___x_4847_ == 0 {
                    lean_dec(v_i_4844_);
                    return v___x_4847_;
                } else {
                    v_k_x27_4848_ = lean_array_fget_borrowed(v_keys_4843_, v_i_4844_);
                    v___x_4849_ = lean_name_eq(v_k_4845_, v_k_x27_4848_);
                    if v___x_4849_ == 0 {
                        v___x_4850_ = lean_unsigned_to_nat(1);
                        v___x_4851_ = lean_nat_add(v_i_4844_, v___x_4850_);
                        lean_dec(v_i_4844_);
                        v_i_4844_ = v___x_4851_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4844_);
                        return v___x_4849_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4853_: *mut LeanObject,
    mut v_i_4854_: *mut LeanObject,
    mut v_k_4855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4856_: u8 = 0;
    let mut v_r_4857_: *mut LeanObject = core::ptr::null_mut();
    v_res_4856_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_4853_, v_i_4854_, v_k_4855_);
    lean_dec(v_k_4855_);
    lean_dec_ref(v_keys_4853_);
    v_r_4857_ = lean_box((v_res_4856_) as usize);
    return v_r_4857_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: usize = 0;
    let mut v___x_4860_: usize = 0;
    v___x_4858_ = 5usize;
    v___x_4859_ = 1usize;
    v___x_4860_ = lean_usize_shift_left(v___x_4859_, v___x_4858_);
    return v___x_4860_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_4861_: usize = 0;
    let mut v___x_4862_: usize = 0;
    let mut v___x_4863_: usize = 0;
    v___x_4861_ = 1usize;
    v___x_4862_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0);
    v___x_4863_ = lean_usize_sub(v___x_4862_, v___x_4861_);
    return v___x_4863_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(
    mut v_x_4864_: *mut LeanObject,
    mut v_x_4865_: usize,
    mut v_x_4866_: *mut LeanObject,
) -> u8 {
    let mut v_es_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: usize = 0;
    let mut v___x_4870_: usize = 0;
    let mut v___x_4871_: usize = 0;
    let mut v_j_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v_node_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: usize = 0;
    let mut v___x_4879_: u8 = 0;
    let mut v_ks_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4864_) == 0 {
                    v_es_4867_ = lean_ctor_get(v_x_4864_, 0);
                    v___x_4868_ = lean_box(2);
                    v___x_4869_ = 5usize;
                    v___x_4870_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
                    v___x_4871_ = lean_usize_land(v_x_4865_, v___x_4870_);
                    v_j_4872_ = lean_usize_to_nat(v___x_4871_);
                    v___x_4873_ = lean_array_get_borrowed(v___x_4868_, v_es_4867_, v_j_4872_);
                    lean_dec(v_j_4872_);
                    match lean_obj_tag(v___x_4873_) {
                        0 => {
                            v_key_4874_ = lean_ctor_get(v___x_4873_, 0);
                            v___x_4875_ = lean_name_eq(v_x_4866_, v_key_4874_);
                            return v___x_4875_;
                        }
                        1 => {
                            v_node_4876_ = lean_ctor_get(v___x_4873_, 0);
                            v___x_4877_ = lean_usize_shift_right(v_x_4865_, v___x_4869_);
                            v_x_4864_ = v_node_4876_;
                            v_x_4865_ = v___x_4877_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4879_ = 0;
                            return v___x_4879_;
                        }
                    }
                } else {
                    v_ks_4880_ = lean_ctor_get(v_x_4864_, 0);
                    v___x_4881_ = lean_unsigned_to_nat(0);
                    v___x_4882_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_4880_, v___x_4881_, v_x_4866_);
                    return v___x_4882_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(
    mut v_x_4883_: *mut LeanObject,
    mut v_x_4884_: *mut LeanObject,
    mut v_x_4885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4174__boxed_4886_: usize = 0;
    let mut v_res_4887_: u8 = 0;
    let mut v_r_4888_: *mut LeanObject = core::ptr::null_mut();
    v_x_4174__boxed_4886_ = lean_unbox_usize(v_x_4884_);
    lean_dec(v_x_4884_);
    v_res_4887_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_4883_, v_x_4174__boxed_4886_, v_x_4885_);
    lean_dec(v_x_4885_);
    lean_dec_ref(v_x_4883_);
    v_r_4888_ = lean_box((v_res_4887_) as usize);
    return v_r_4888_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: u64 = 0;
    v___x_4889_ = lean_unsigned_to_nat(1723);
    v___x_4890_ = lean_uint64_of_nat(v___x_4889_);
    return v___x_4890_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(
    mut v_x_4891_: *mut LeanObject,
    mut v_x_4892_: *mut LeanObject,
) -> u8 {
    let mut v___y_4894_: u64 = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: u8 = 0;
    let mut v___x_4897_: u64 = 0;
    let mut v_hash_4898_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4892_) == 0 {
                    v___x_4897_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
                    v___y_4894_ = v___x_4897_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4898_ = lean_ctor_get_uint64(
                        v_x_4892_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4894_ = v_hash_4898_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4895_ = lean_uint64_to_usize(v___y_4894_);
                v___x_4896_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_4891_, v___x_4895_, v_x_4892_);
                return v___x_4896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(
    mut v_x_4899_: *mut LeanObject,
    mut v_x_4900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4901_: u8 = 0;
    let mut v_r_4902_: *mut LeanObject = core::ptr::null_mut();
    v_res_4901_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_4899_, v_x_4900_);
    lean_dec(v_x_4900_);
    lean_dec_ref(v_x_4899_);
    v_r_4902_ = lean_box((v_res_4901_) as usize);
    return v_r_4902_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(
    mut v_tactics_4903_: *mut LeanObject,
    mut v_a_4904_: *mut LeanObject,
    mut v___x_4905_: u8,
    mut v_x_4906_: *mut LeanObject,
    mut v_____s_4907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kinds_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: u8 = 0;
    v_fst_4908_ = lean_ctor_get(v_x_4906_, 0);
    lean_inc(v_fst_4908_);
    lean_dec_ref(v_x_4906_);
    v_kinds_4909_ = lean_ctor_get(v_tactics_4903_, 1);
    v___x_4910_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_4909_, v_fst_4908_);
    if v___x_4910_ == 0 {
        let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_4908_);
        lean_dec(v_a_4904_);
        v___x_4911_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4911_, 0, v_____s_4907_);
        return v___x_4911_;
    } else {
        let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
        v___x_4912_ = l_Lean_Name_toString(v_a_4904_, v___x_4905_);
        v___x_4913_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_4912_, v_fst_4908_, v_____s_4907_);
        v___x_4914_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4914_, 0, v___x_4913_);
        return v___x_4914_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(
    mut v_tactics_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
    mut v___x_4917_: *mut LeanObject,
    mut v_x_4918_: *mut LeanObject,
    mut v_____s_4919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4242__boxed_4920_: u8 = 0;
    let mut v_res_4921_: *mut LeanObject = core::ptr::null_mut();
    v___x_4242__boxed_4920_ = (lean_unbox(v___x_4917_) as u8);
    v_res_4921_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_4915_, v_a_4916_, v___x_4242__boxed_4920_, v_x_4918_, v_____s_4919_);
    lean_dec_ref(v_tactics_4915_);
    return v_res_4921_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(
    mut v_f_4922_: *mut LeanObject,
    mut v_keys_4923_: *mut LeanObject,
    mut v_vals_4924_: *mut LeanObject,
    mut v_i_4925_: *mut LeanObject,
    mut v_acc_4926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4927_ = lean_array_get_size(v_keys_4923_);
                v___x_4928_ = lean_nat_dec_lt(v_i_4925_, v___x_4927_);
                if v___x_4928_ == 0 {
                    lean_dec(v_i_4925_);
                    lean_dec_ref(v_f_4922_);
                    v___x_4929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4929_, 0, v_acc_4926_);
                    return v___x_4929_;
                } else {
                    v_k_4930_ = lean_array_fget_borrowed(v_keys_4923_, v_i_4925_);
                    v_v_4931_ = lean_array_fget_borrowed(v_vals_4924_, v_i_4925_);
                    lean_inc_ref(v_f_4922_);
                    lean_inc(v_v_4931_);
                    lean_inc(v_k_4930_);
                    v___x_4932_ = lean_apply_3(v_f_4922_, v_acc_4926_, v_k_4930_, v_v_4931_);
                    if lean_obj_tag(v___x_4932_) == 0 {
                        lean_dec(v_i_4925_);
                        lean_dec_ref(v_f_4922_);
                        return v___x_4932_;
                    } else {
                        v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
                        lean_inc(v_a_4933_);
                        lean_dec_ref_known(v___x_4932_, 1);
                        v___x_4934_ = lean_unsigned_to_nat(1);
                        v___x_4935_ = lean_nat_add(v_i_4925_, v___x_4934_);
                        lean_dec(v_i_4925_);
                        v_i_4925_ = v___x_4935_;
                        v_acc_4926_ = v_a_4933_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_f_4937_: *mut LeanObject,
    mut v_keys_4938_: *mut LeanObject,
    mut v_vals_4939_: *mut LeanObject,
    mut v_i_4940_: *mut LeanObject,
    mut v_acc_4941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4942_: *mut LeanObject = core::ptr::null_mut();
    v_res_4942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_4937_, v_keys_4938_, v_vals_4939_, v_i_4940_, v_acc_4941_);
    lean_dec_ref(v_vals_4939_);
    lean_dec_ref(v_keys_4938_);
    return v_res_4942_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(
    mut v_f_4943_: *mut LeanObject,
    mut v_x_4944_: *mut LeanObject,
    mut v_x_4945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: usize = 0;
    let mut v___x_4961_: usize = 0;
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: usize = 0;
    let mut v___x_4964_: usize = 0;
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v_ks_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4944_) == 0 {
                    v_es_4946_ = lean_ctor_get(v_x_4944_, 0);
                    v_isSharedCheck_4966_ = (!lean_is_exclusive(v_x_4944_)) as u8;
                    if v_isSharedCheck_4966_ == 0 {
                        v___x_4948_ = v_x_4944_;
                        v_isShared_4949_ = v_isSharedCheck_4966_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_4946_);
                        lean_dec(v_x_4944_);
                        v___x_4948_ = lean_box(0);
                        v_isShared_4949_ = v_isSharedCheck_4966_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_4967_ = lean_ctor_get(v_x_4944_, 0);
                    lean_inc_ref(v_ks_4967_);
                    v_vs_4968_ = lean_ctor_get(v_x_4944_, 1);
                    lean_inc_ref(v_vs_4968_);
                    lean_dec_ref_known(v_x_4944_, 2);
                    v___x_4969_ = lean_unsigned_to_nat(0);
                    v___x_4970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_4943_, v_ks_4967_, v_vs_4968_, v___x_4969_, v_x_4945_);
                    lean_dec_ref(v_vs_4968_);
                    lean_dec_ref(v_ks_4967_);
                    return v___x_4970_;
                }
            }
            1 => {
                v___x_4950_ = lean_unsigned_to_nat(0);
                v___x_4951_ = lean_array_get_size(v_es_4946_);
                v___x_4952_ = lean_nat_dec_lt(v___x_4950_, v___x_4951_);
                if v___x_4952_ == 0 {
                    lean_dec_ref(v_es_4946_);
                    lean_dec_ref(v_f_4943_);
                    if v_isShared_4949_ == 0 {
                        lean_ctor_set_tag(v___x_4948_, 1);
                        lean_ctor_set(v___x_4948_, 0, v_x_4945_);
                        v___x_4954_ = v___x_4948_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_x_4945_);
                        v___x_4954_ = v_reuseFailAlloc_4955_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4956_ = lean_nat_dec_le(v___x_4951_, v___x_4951_);
                    if v___x_4956_ == 0 {
                        if v___x_4952_ == 0 {
                            lean_dec_ref(v_es_4946_);
                            lean_dec_ref(v_f_4943_);
                            if v_isShared_4949_ == 0 {
                                lean_ctor_set_tag(v___x_4948_, 1);
                                lean_ctor_set(v___x_4948_, 0, v_x_4945_);
                                v___x_4958_ = v___x_4948_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_x_4945_);
                                v___x_4958_ = v_reuseFailAlloc_4959_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4948_);
                            v___x_4960_ = 0usize;
                            v___x_4961_ = lean_usize_of_nat(v___x_4951_);
                            v___x_4962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_4943_, v_es_4946_, v___x_4960_, v___x_4961_, v_x_4945_);
                            lean_dec_ref(v_es_4946_);
                            return v___x_4962_;
                        }
                    } else {
                        lean_del_object(v___x_4948_);
                        v___x_4963_ = 0usize;
                        v___x_4964_ = lean_usize_of_nat(v___x_4951_);
                        v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_4943_, v_es_4946_, v___x_4963_, v___x_4964_, v_x_4945_);
                        lean_dec_ref(v_es_4946_);
                        return v___x_4965_;
                    }
                }
            }
            2 => {
                return v___x_4954_;
            }
            3 => {
                return v___x_4958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(
    mut v_f_4971_: *mut LeanObject,
    mut v_as_4972_: *mut LeanObject,
    mut v_i_4973_: usize,
    mut v_stop_4974_: usize,
    mut v_b_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: usize = 0;
    let mut v___x_4979_: usize = 0;
    let mut v___y_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4984_ = lean_usize_dec_eq(v_i_4973_, v_stop_4974_);
                if v___x_4984_ == 0 {
                    v___x_4985_ = lean_array_uget_borrowed(v_as_4972_, v_i_4973_);
                    match lean_obj_tag(v___x_4985_) {
                        0 => {
                            v_key_4986_ = lean_ctor_get(v___x_4985_, 0);
                            v_val_4987_ = lean_ctor_get(v___x_4985_, 1);
                            lean_inc_ref(v_f_4971_);
                            lean_inc(v_val_4987_);
                            lean_inc(v_key_4986_);
                            v___x_4988_ =
                                lean_apply_3(v_f_4971_, v_b_4975_, v_key_4986_, v_val_4987_);
                            v___y_4982_ = v___x_4988_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_4989_ = lean_ctor_get(v___x_4985_, 0);
                            lean_inc(v_node_4989_);
                            lean_inc_ref(v_f_4971_);
                            v___x_4990_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_4971_, v_node_4989_, v_b_4975_);
                            v___y_4982_ = v___x_4990_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_4977_ = v_b_4975_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_4971_);
                    v___x_4991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4991_, 0, v_b_4975_);
                    return v___x_4991_;
                }
            }
            1 => {
                v___x_4978_ = 1usize;
                v___x_4979_ = lean_usize_add(v_i_4973_, v___x_4978_);
                v_i_4973_ = v___x_4979_;
                v_b_4975_ = v_a_4977_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_4982_) == 0 {
                    lean_dec_ref(v_f_4971_);
                    return v___y_4982_;
                } else {
                    v_a_4983_ = lean_ctor_get(v___y_4982_, 0);
                    lean_inc(v_a_4983_);
                    lean_dec_ref_known(v___y_4982_, 1);
                    v_a_4977_ = v_a_4983_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_f_4992_: *mut LeanObject,
    mut v_as_4993_: *mut LeanObject,
    mut v_i_4994_: *mut LeanObject,
    mut v_stop_4995_: *mut LeanObject,
    mut v_b_4996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4997_: usize = 0;
    let mut v_stop_boxed_4998_: usize = 0;
    let mut v_res_4999_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4997_ = lean_unbox_usize(v_i_4994_);
    lean_dec(v_i_4994_);
    v_stop_boxed_4998_ = lean_unbox_usize(v_stop_4995_);
    lean_dec(v_stop_4995_);
    v_res_4999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_4992_, v_as_4993_, v_i_boxed_4997_, v_stop_boxed_4998_, v_b_4996_);
    lean_dec_ref(v_as_4993_);
    return v_res_4999_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(
    mut v_f_5000_: *mut LeanObject,
    mut v_s_5001_: *mut LeanObject,
    mut v_a_5002_: *mut LeanObject,
    mut v_b_5003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5009_: u8 = 0;
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5013_: u8 = 0;
    let mut v_a_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5017_: u8 = 0;
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5004_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5004_, 0, v_a_5002_);
                lean_ctor_set(v___x_5004_, 1, v_b_5003_);
                v___x_5005_ = lean_apply_2(v_f_5000_, v___x_5004_, v_s_5001_);
                if lean_obj_tag(v___x_5005_) == 0 {
                    v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
                    v_isSharedCheck_5013_ = (!lean_is_exclusive(v___x_5005_)) as u8;
                    if v_isSharedCheck_5013_ == 0 {
                        v___x_5008_ = v___x_5005_;
                        v_isShared_5009_ = v_isSharedCheck_5013_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5006_);
                        lean_dec(v___x_5005_);
                        v___x_5008_ = lean_box(0);
                        v_isShared_5009_ = v_isSharedCheck_5013_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5014_ = lean_ctor_get(v___x_5005_, 0);
                    v_isSharedCheck_5021_ = (!lean_is_exclusive(v___x_5005_)) as u8;
                    if v_isSharedCheck_5021_ == 0 {
                        v___x_5016_ = v___x_5005_;
                        v_isShared_5017_ = v_isSharedCheck_5021_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5014_);
                        lean_dec(v___x_5005_);
                        v___x_5016_ = lean_box(0);
                        v_isShared_5017_ = v_isSharedCheck_5021_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5009_ == 0 {
                    v___x_5011_ = v___x_5008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
                    v___x_5011_ = v_reuseFailAlloc_5012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5011_;
            }
            3 => {
                if v_isShared_5017_ == 0 {
                    v___x_5019_ = v___x_5016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
                    v___x_5019_ = v_reuseFailAlloc_5020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(
    mut v_map_5022_: *mut LeanObject,
    mut v_init_5023_: *mut LeanObject,
    mut v_f_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5027_: *mut LeanObject = core::ptr::null_mut();
    v___f_5025_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_5025_, 0, v_f_5024_);
    lean_inc_ref(v_map_5022_);
    v___x_5026_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_5025_, v_map_5022_, v_init_5023_);
    v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
    lean_inc(v_a_5027_);
    lean_dec_ref(v___x_5026_);
    return v_a_5027_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(
    mut v_map_5028_: *mut LeanObject,
    mut v_init_5029_: *mut LeanObject,
    mut v_f_5030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5031_: *mut LeanObject = core::ptr::null_mut();
    v_res_5031_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_5028_, v_init_5029_, v_f_5030_);
    lean_dec_ref(v_map_5028_);
    return v_res_5031_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    v___x_5032_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5032_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    v___x_5033_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
    v___x_5034_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5034_, 0, v___x_5033_);
    return v___x_5034_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(
    mut v_tactics_5035_: *mut LeanObject,
    mut v_a_5036_: *mut LeanObject,
    mut v___x_5037_: u8,
    mut v_as_x27_5038_: *mut LeanObject,
    mut v_b_5039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_collectKinds_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5038_) == 0 {
                    lean_dec(v_a_5036_);
                    lean_dec_ref(v_tactics_5035_);
                    return v_b_5039_;
                } else {
                    v_head_5040_ = lean_ctor_get(v_as_x27_5038_, 0);
                    v_fst_5041_ = lean_ctor_get(v_head_5040_, 0);
                    v_info_5042_ = lean_ctor_get(v_fst_5041_, 0);
                    v_tail_5043_ = lean_ctor_get(v_as_x27_5038_, 1);
                    v_collectKinds_5044_ = lean_ctor_get(v_info_5042_, 1);
                    v___x_5045_ = lean_box((v___x_5037_) as usize);
                    lean_inc(v_a_5036_);
                    lean_inc_ref(v_tactics_5035_);
                    v___f_5046_ = lean_alloc_closure(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_5046_, 0, v_tactics_5035_);
                    lean_closure_set(v___f_5046_, 1, v_a_5036_);
                    lean_closure_set(v___f_5046_, 2, v___x_5045_);
                    v___x_5047_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
                    lean_inc_ref(v_collectKinds_5044_);
                    v___x_5048_ = lean_apply_1(v_collectKinds_5044_, v___x_5047_);
                    v___x_5049_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_5048_, v_b_5039_, v___f_5046_);
                    lean_dec_ref(v___x_5048_);
                    v_as_x27_5038_ = v_tail_5043_;
                    v_b_5039_ = v___x_5049_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(
    mut v_tactics_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
    mut v___x_5053_: *mut LeanObject,
    mut v_as_x27_5054_: *mut LeanObject,
    mut v_b_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4416__boxed_5056_: u8 = 0;
    let mut v_res_5057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416__boxed_5056_ = (lean_unbox(v___x_5053_) as u8);
    v_res_5057_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_5051_, v_a_5052_, v___x_4416__boxed_5056_, v_as_x27_5054_, v_b_5055_);
    lean_dec(v_as_x27_5054_);
    return v_res_5057_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(
    mut v_tactics_5061_: *mut LeanObject,
    mut v_init_5062_: *mut LeanObject,
    mut v_x_5063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u8 = 0;
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5063_) == 0 {
                    v_k_5064_ = lean_ctor_get(v_x_5063_, 1);
                    lean_inc(v_k_5064_);
                    v_v_5065_ = lean_ctor_get(v_x_5063_, 2);
                    lean_inc(v_v_5065_);
                    v_l_5066_ = lean_ctor_get(v_x_5063_, 3);
                    lean_inc(v_l_5066_);
                    v_r_5067_ = lean_ctor_get(v_x_5063_, 4);
                    lean_inc(v_r_5067_);
                    lean_dec_ref_known(v_x_5063_, 5);
                    lean_inc_ref(v_tactics_5061_);
                    v___x_5068_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_5061_, v_init_5062_, v_l_5066_);
                    v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
                    lean_inc(v_a_5069_);
                    v___x_5070_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1;
                    v___x_5071_ = lean_name_eq(v_k_5064_, v___x_5070_);
                    if v___x_5071_ == 0 {
                        lean_dec_ref(v___x_5068_);
                        lean_inc_ref(v_tactics_5061_);
                        v___x_5072_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_5061_, v_k_5064_, v___x_5071_, v_v_5065_, v_a_5069_);
                        lean_dec(v_v_5065_);
                        v_init_5062_ = v___x_5072_;
                        v_x_5063_ = v_r_5067_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_5069_);
                        lean_dec(v_v_5065_);
                        lean_dec(v_k_5064_);
                        v_a_5074_ = lean_ctor_get(v___x_5068_, 0);
                        lean_inc(v_a_5074_);
                        lean_dec_ref(v___x_5068_);
                        v_init_5062_ = v_a_5074_;
                        v_x_5063_ = v_r_5067_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_tactics_5061_);
                    v___x_5076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5076_, 0, v_init_5062_);
                    return v___x_5076_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(
    mut v_tactics_5077_: *mut LeanObject,
    mut v_table_5078_: *mut LeanObject,
    mut v_firsts_5079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5080_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_5077_, v_firsts_5079_, v_table_5078_);
    v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
    lean_inc(v_a_5081_);
    lean_dec_ref(v___x_5080_);
    return v_a_5081_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(
    mut v_00_u03b2_5082_: *mut LeanObject,
    mut v_x_5083_: *mut LeanObject,
    mut v_x_5084_: *mut LeanObject,
) -> u8 {
    let mut v___x_5085_: u8 = 0;
    v___x_5085_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_5083_, v_x_5084_);
    return v___x_5085_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(
    mut v_00_u03b2_5086_: *mut LeanObject,
    mut v_x_5087_: *mut LeanObject,
    mut v_x_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5089_: u8 = 0;
    let mut v_r_5090_: *mut LeanObject = core::ptr::null_mut();
    v_res_5089_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_5086_, v_x_5087_, v_x_5088_);
    lean_dec(v_x_5088_);
    lean_dec_ref(v_x_5087_);
    v_r_5090_ = lean_box((v_res_5089_) as usize);
    return v_r_5090_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(
    mut v___x_5091_: *mut LeanObject,
    mut v_k_5092_: *mut LeanObject,
    mut v_t_5093_: *mut LeanObject,
    mut v_hl_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    v___x_5095_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_5091_, v_k_5092_, v_t_5093_);
    return v___x_5095_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(
    mut v_00_u03c3_5096_: *mut LeanObject,
    mut v_00_u03b2_5097_: *mut LeanObject,
    mut v_map_5098_: *mut LeanObject,
    mut v_init_5099_: *mut LeanObject,
    mut v_f_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    v___x_5101_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_5098_, v_init_5099_, v_f_5100_);
    return v___x_5101_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(
    mut v_00_u03c3_5102_: *mut LeanObject,
    mut v_00_u03b2_5103_: *mut LeanObject,
    mut v_map_5104_: *mut LeanObject,
    mut v_init_5105_: *mut LeanObject,
    mut v_f_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5107_: *mut LeanObject = core::ptr::null_mut();
    v_res_5107_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_5102_, v_00_u03b2_5103_, v_map_5104_, v_init_5105_, v_f_5106_);
    lean_dec_ref(v_map_5104_);
    return v_res_5107_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(
    mut v_tactics_5108_: *mut LeanObject,
    mut v_a_5109_: *mut LeanObject,
    mut v___x_5110_: u8,
    mut v_as_5111_: *mut LeanObject,
    mut v_as_x27_5112_: *mut LeanObject,
    mut v_b_5113_: *mut LeanObject,
    mut v_a_5114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    v___x_5115_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_5108_, v_a_5109_, v___x_5110_, v_as_x27_5112_, v_b_5113_);
    return v___x_5115_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(
    mut v_tactics_5116_: *mut LeanObject,
    mut v_a_5117_: *mut LeanObject,
    mut v___x_5118_: *mut LeanObject,
    mut v_as_5119_: *mut LeanObject,
    mut v_as_x27_5120_: *mut LeanObject,
    mut v_b_5121_: *mut LeanObject,
    mut v_a_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4499__boxed_5123_: u8 = 0;
    let mut v_res_5124_: *mut LeanObject = core::ptr::null_mut();
    v___x_4499__boxed_5123_ = (lean_unbox(v___x_5118_) as u8);
    v_res_5124_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_5116_, v_a_5117_, v___x_4499__boxed_5123_, v_as_5119_, v_as_x27_5120_, v_b_5121_, v_a_5122_);
    lean_dec(v_as_x27_5120_);
    lean_dec(v_as_5119_);
    return v_res_5124_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(
    mut v_00_u03b2_5125_: *mut LeanObject,
    mut v_x_5126_: *mut LeanObject,
    mut v_x_5127_: usize,
    mut v_x_5128_: *mut LeanObject,
) -> u8 {
    let mut v___x_5129_: u8 = 0;
    v___x_5129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_5126_, v_x_5127_, v_x_5128_);
    return v___x_5129_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(
    mut v_00_u03b2_5130_: *mut LeanObject,
    mut v_x_5131_: *mut LeanObject,
    mut v_x_5132_: *mut LeanObject,
    mut v_x_5133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4508__boxed_5134_: usize = 0;
    let mut v_res_5135_: u8 = 0;
    let mut v_r_5136_: *mut LeanObject = core::ptr::null_mut();
    v_x_4508__boxed_5134_ = lean_unbox_usize(v_x_5132_);
    lean_dec(v_x_5132_);
    v_res_5135_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_5130_, v_x_5131_, v_x_4508__boxed_5134_, v_x_5133_);
    lean_dec(v_x_5133_);
    lean_dec_ref(v_x_5131_);
    v_r_5136_ = lean_box((v_res_5135_) as usize);
    return v_r_5136_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(
    mut v_map_5137_: *mut LeanObject,
    mut v_f_5138_: *mut LeanObject,
    mut v_init_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    v___x_5140_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_5138_, v_map_5137_, v_init_5139_);
    return v___x_5140_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(
    mut v_00_u03c3_5141_: *mut LeanObject,
    mut v_00_u03c3_5142_: *mut LeanObject,
    mut v_00_u03b2_5143_: *mut LeanObject,
    mut v_map_5144_: *mut LeanObject,
    mut v_f_5145_: *mut LeanObject,
    mut v_init_5146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    v___x_5147_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_5145_, v_map_5144_, v_init_5146_);
    return v___x_5147_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5148_: *mut LeanObject,
    mut v_keys_5149_: *mut LeanObject,
    mut v_vals_5150_: *mut LeanObject,
    mut v_heq_5151_: *mut LeanObject,
    mut v_i_5152_: *mut LeanObject,
    mut v_k_5153_: *mut LeanObject,
) -> u8 {
    let mut v___x_5154_: u8 = 0;
    v___x_5154_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_5149_, v_i_5152_, v_k_5153_);
    return v___x_5154_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5155_: *mut LeanObject,
    mut v_keys_5156_: *mut LeanObject,
    mut v_vals_5157_: *mut LeanObject,
    mut v_heq_5158_: *mut LeanObject,
    mut v_i_5159_: *mut LeanObject,
    mut v_k_5160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5161_: u8 = 0;
    let mut v_r_5162_: *mut LeanObject = core::ptr::null_mut();
    v_res_5161_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_5155_, v_keys_5156_, v_vals_5157_, v_heq_5158_, v_i_5159_, v_k_5160_);
    lean_dec(v_k_5160_);
    lean_dec_ref(v_vals_5157_);
    lean_dec_ref(v_keys_5156_);
    v_r_5162_ = lean_box((v_res_5161_) as usize);
    return v_r_5162_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(
    mut v_00_u03c3_5163_: *mut LeanObject,
    mut v_00_u03c3_5164_: *mut LeanObject,
    mut v_00_u03b1_5165_: *mut LeanObject,
    mut v_00_u03b2_5166_: *mut LeanObject,
    mut v_f_5167_: *mut LeanObject,
    mut v_x_5168_: *mut LeanObject,
    mut v_x_5169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    v___x_5170_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_5167_, v_x_5168_, v_x_5169_);
    return v___x_5170_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(
    mut v_00_u03b1_5171_: *mut LeanObject,
    mut v_00_u03b2_5172_: *mut LeanObject,
    mut v_00_u03c3_5173_: *mut LeanObject,
    mut v_00_u03c3_5174_: *mut LeanObject,
    mut v_f_5175_: *mut LeanObject,
    mut v_as_5176_: *mut LeanObject,
    mut v_i_5177_: usize,
    mut v_stop_5178_: usize,
    mut v_b_5179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    v___x_5180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_5175_, v_as_5176_, v_i_5177_, v_stop_5178_, v_b_5179_);
    return v___x_5180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b1_5181_: *mut LeanObject,
    mut v_00_u03b2_5182_: *mut LeanObject,
    mut v_00_u03c3_5183_: *mut LeanObject,
    mut v_00_u03c3_5184_: *mut LeanObject,
    mut v_f_5185_: *mut LeanObject,
    mut v_as_5186_: *mut LeanObject,
    mut v_i_5187_: *mut LeanObject,
    mut v_stop_5188_: *mut LeanObject,
    mut v_b_5189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5190_: usize = 0;
    let mut v_stop_boxed_5191_: usize = 0;
    let mut v_res_5192_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5190_ = lean_unbox_usize(v_i_5187_);
    lean_dec(v_i_5187_);
    v_stop_boxed_5191_ = lean_unbox_usize(v_stop_5188_);
    lean_dec(v_stop_5188_);
    v_res_5192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_5181_, v_00_u03b2_5182_, v_00_u03c3_5183_, v_00_u03c3_5184_, v_f_5185_, v_as_5186_, v_i_boxed_5190_, v_stop_boxed_5191_, v_b_5189_);
    lean_dec_ref(v_as_5186_);
    return v_res_5192_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(
    mut v_00_u03c3_5193_: *mut LeanObject,
    mut v_00_u03c3_5194_: *mut LeanObject,
    mut v_00_u03b1_5195_: *mut LeanObject,
    mut v_00_u03b2_5196_: *mut LeanObject,
    mut v_f_5197_: *mut LeanObject,
    mut v_keys_5198_: *mut LeanObject,
    mut v_vals_5199_: *mut LeanObject,
    mut v_heq_5200_: *mut LeanObject,
    mut v_i_5201_: *mut LeanObject,
    mut v_acc_5202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    v___x_5203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_5197_, v_keys_5198_, v_vals_5199_, v_i_5201_, v_acc_5202_);
    return v___x_5203_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(
    mut v_00_u03c3_5204_: *mut LeanObject,
    mut v_00_u03c3_5205_: *mut LeanObject,
    mut v_00_u03b1_5206_: *mut LeanObject,
    mut v_00_u03b2_5207_: *mut LeanObject,
    mut v_f_5208_: *mut LeanObject,
    mut v_keys_5209_: *mut LeanObject,
    mut v_vals_5210_: *mut LeanObject,
    mut v_heq_5211_: *mut LeanObject,
    mut v_i_5212_: *mut LeanObject,
    mut v_acc_5213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5214_: *mut LeanObject = core::ptr::null_mut();
    v_res_5214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_5204_, v_00_u03c3_5205_, v_00_u03b1_5206_, v_00_u03b2_5207_, v_f_5208_, v_keys_5209_, v_vals_5210_, v_heq_5211_, v_i_5212_, v_acc_5213_);
    lean_dec_ref(v_vals_5210_);
    lean_dec_ref(v_keys_5209_);
    return v_res_5214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(
    mut v_x1_5215_: *mut LeanObject,
    mut v_x2_5216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    v_fst_5217_ = lean_ctor_get(v_x2_5216_, 0);
    lean_inc(v_fst_5217_);
    v_snd_5218_ = lean_ctor_get(v_x2_5216_, 1);
    lean_inc(v_snd_5218_);
    lean_dec_ref(v_x2_5216_);
    v___x_5219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_5217_,
        v_snd_5218_,
        v_x1_5215_,
    );
    return v___x_5219_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(
    mut v___f_5239_: *mut LeanObject,
    mut v_x1_5240_: *mut LeanObject,
    mut v_x2_5241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    v___x_5242_ = lean_unsigned_to_nat(0);
    v___x_5243_ = lean_array_get_size(v_x2_5241_);
    v___x_5244_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9;
    v___x_5245_ = lean_nat_dec_lt(v___x_5242_, v___x_5243_);
    if v___x_5245_ == 0 {
        lean_dec_ref(v_x2_5241_);
        lean_dec_ref(v___f_5239_);
        return v_x1_5240_;
    } else {
        let mut v___x_5246_: u8 = 0;
        v___x_5246_ = lean_nat_dec_le(v___x_5243_, v___x_5243_);
        if v___x_5246_ == 0 {
            if v___x_5245_ == 0 {
                lean_dec_ref(v_x2_5241_);
                lean_dec_ref(v___f_5239_);
                return v_x1_5240_;
            } else {
                let mut v___x_5247_: usize = 0;
                let mut v___x_5248_: usize = 0;
                let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
                v___x_5247_ = 0usize;
                v___x_5248_ = lean_usize_of_nat(v___x_5243_);
                v___x_5249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_5244_,
                    v___f_5239_,
                    v_x2_5241_,
                    v___x_5247_,
                    v___x_5248_,
                    v_x1_5240_,
                );
                return v___x_5249_;
            }
        } else {
            let mut v___x_5250_: usize = 0;
            let mut v___x_5251_: usize = 0;
            let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
            v___x_5250_ = 0usize;
            v___x_5251_ = lean_usize_of_nat(v___x_5243_);
            v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_5244_,
                v___f_5239_,
                v_x2_5241_,
                v___x_5250_,
                v___x_5251_,
                v_x1_5240_,
            );
            return v___x_5252_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(
    mut v___x_5256_: *mut LeanObject,
    mut v___x_5257_: *mut LeanObject,
    mut v___x_5258_: *mut LeanObject,
    mut v___x_5259_: *mut LeanObject,
    mut v___x_5260_: *mut LeanObject,
    mut v_toPure_5261_: *mut LeanObject,
    mut v___f_5262_: *mut LeanObject,
    mut v_env_5263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_categories_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tables_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadingTable_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trailingTable_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstTokens_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstTokens_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: u8 = 0;
    let mut v___x_5297_: u8 = 0;
    let mut v___x_5298_: usize = 0;
    let mut v___x_5299_: usize = 0;
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: usize = 0;
    let mut v___x_5302_: usize = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5264_ = l_Lean_Parser_parserExtension;
                v_ext_5265_ = lean_ctor_get(v___x_5264_, 1);
                v_toEnvExtension_5266_ = lean_ctor_get(v_ext_5265_, 0);
                v_asyncMode_5267_ = lean_ctor_get(v_toEnvExtension_5266_, 2);
                lean_inc_ref(v_env_5263_);
                v___x_5268_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_5256_,
                    v___x_5264_,
                    v_env_5263_,
                    v_asyncMode_5267_,
                );
                v_categories_5269_ = lean_ctor_get(v___x_5268_, 2);
                lean_inc_ref(v_categories_5269_);
                lean_dec(v___x_5268_);
                v___x_5270_ =
                    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1;
                v___x_5271_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_5257_,
                    v___x_5258_,
                    v_categories_5269_,
                    v___x_5270_,
                );
                lean_dec_ref(v_categories_5269_);
                if lean_obj_tag(v___x_5271_) == 1 {
                    v_val_5272_ = lean_ctor_get(v___x_5271_, 0);
                    lean_inc(v_val_5272_);
                    lean_dec_ref_known(v___x_5271_, 1);
                    v___x_5281_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
                    v_toEnvExtension_5282_ = lean_ctor_get(v___x_5281_, 0);
                    v_exportEntriesFn_5283_ = lean_ctor_get(v___x_5281_, 4);
                    v_asyncMode_5284_ = lean_ctor_get(v_toEnvExtension_5282_, 2);
                    v___x_5285_ = lean_box(0);
                    lean_inc_ref_n(v_env_5263_, 2);
                    v___x_5286_ =
                        l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                            v___x_5259_,
                            v_toEnvExtension_5282_,
                            v_env_5263_,
                            v_asyncMode_5284_,
                            v___x_5285_,
                        );
                    v_importedEntries_5287_ = lean_ctor_get(v___x_5286_, 0);
                    lean_inc_ref(v_importedEntries_5287_);
                    lean_dec(v___x_5286_);
                    v___x_5288_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_5260_,
                        v___x_5281_,
                        v_env_5263_,
                        v_asyncMode_5284_,
                        v___x_5285_,
                    );
                    lean_inc_ref(v_exportEntriesFn_5283_);
                    v___x_5289_ = lean_apply_2(v_exportEntriesFn_5283_, v_env_5263_, v___x_5288_);
                    v_exported_5290_ = lean_ctor_get(v___x_5289_, 0);
                    lean_inc(v_exported_5290_);
                    lean_dec_ref(v___x_5289_);
                    v___x_5291_ = lean_box(1);
                    v___x_5292_ = lean_array_push(v_importedEntries_5287_, v_exported_5290_);
                    v___x_5293_ = lean_unsigned_to_nat(0);
                    v___x_5294_ = lean_array_get_size(v___x_5292_);
                    v___x_5295_ =
                        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9;
                    v___x_5296_ = lean_nat_dec_lt(v___x_5293_, v___x_5294_);
                    if v___x_5296_ == 0 {
                        lean_dec_ref(v___x_5292_);
                        lean_dec_ref(v___f_5262_);
                        v___y_5274_ = v___x_5291_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5297_ = lean_nat_dec_le(v___x_5294_, v___x_5294_);
                        if v___x_5297_ == 0 {
                            if v___x_5296_ == 0 {
                                lean_dec_ref(v___x_5292_);
                                lean_dec_ref(v___f_5262_);
                                v___y_5274_ = v___x_5291_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5298_ = 0usize;
                                v___x_5299_ = lean_usize_of_nat(v___x_5294_);
                                v___x_5300_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_5295_,
                                        v___f_5262_,
                                        v___x_5292_,
                                        v___x_5298_,
                                        v___x_5299_,
                                        v___x_5291_,
                                    );
                                v___y_5274_ = v___x_5300_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_5301_ = 0usize;
                            v___x_5302_ = lean_usize_of_nat(v___x_5294_);
                            v___x_5303_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_5295_,
                                    v___f_5262_,
                                    v___x_5292_,
                                    v___x_5301_,
                                    v___x_5302_,
                                    v___x_5291_,
                                );
                            v___y_5274_ = v___x_5303_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5271_);
                    lean_dec_ref(v_env_5263_);
                    lean_dec_ref(v___f_5262_);
                    lean_dec(v___x_5260_);
                    v___x_5304_ = lean_box(1);
                    v___x_5305_ = lean_apply_2(v_toPure_5261_, lean_box(0), v___x_5304_);
                    return v___x_5305_;
                }
            }
            1 => {
                v_tables_5275_ = lean_ctor_get(v_val_5272_, 2);
                v_leadingTable_5276_ = lean_ctor_get(v_tables_5275_, 0);
                v_trailingTable_5277_ = lean_ctor_get(v_tables_5275_, 2);
                lean_inc(v_trailingTable_5277_);
                lean_inc(v_leadingTable_5276_);
                lean_inc(v_val_5272_);
                v_firstTokens_5278_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_5272_, v_leadingTable_5276_, v___y_5274_);
                v_firstTokens_5279_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_5272_, v_trailingTable_5277_, v_firstTokens_5278_);
                v___x_5280_ = lean_apply_2(v_toPure_5261_, lean_box(0), v_firstTokens_5279_);
                return v___x_5280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(
    mut v___x_5306_: *mut LeanObject,
    mut v___x_5307_: *mut LeanObject,
    mut v___x_5308_: *mut LeanObject,
    mut v___x_5309_: *mut LeanObject,
    mut v___x_5310_: *mut LeanObject,
    mut v_toPure_5311_: *mut LeanObject,
    mut v___f_5312_: *mut LeanObject,
    mut v_env_5313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5314_: *mut LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(
        v___x_5306_,
        v___x_5307_,
        v___x_5308_,
        v___x_5309_,
        v___x_5310_,
        v_toPure_5311_,
        v___f_5312_,
        v_env_5313_,
    );
    lean_dec_ref(v___x_5309_);
    lean_dec_ref(v___x_5306_);
    return v_res_5314_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    v___x_5318_ = lean_box(1);
    v___x_5319_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_5318_);
    return v___x_5319_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(
    mut v_inst_5322_: *mut LeanObject,
    mut v_inst_5323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5324_ = lean_ctor_get(v_inst_5322_, 0);
    lean_inc_ref(v_toApplicative_5324_);
    v_toBind_5325_ = lean_ctor_get(v_inst_5322_, 1);
    lean_inc(v_toBind_5325_);
    lean_dec_ref(v_inst_5322_);
    v_getEnv_5326_ = lean_ctor_get(v_inst_5323_, 0);
    lean_inc(v_getEnv_5326_);
    lean_dec_ref(v_inst_5323_);
    v_toPure_5327_ = lean_ctor_get(v_toApplicative_5324_, 1);
    lean_inc(v_toPure_5327_);
    lean_dec_ref(v_toApplicative_5324_);
    v___f_5328_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1;
    v___x_5329_ = lean_box(1);
    v___x_5330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2,
    );
    v___x_5331_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3;
    v___x_5332_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4;
    v___x_5333_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
    v___f_5334_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_5334_, 0, v___x_5333_);
    lean_closure_set(v___f_5334_, 1, v___x_5331_);
    lean_closure_set(v___f_5334_, 2, v___x_5332_);
    lean_closure_set(v___f_5334_, 3, v___x_5330_);
    lean_closure_set(v___f_5334_, 4, v___x_5329_);
    lean_closure_set(v___f_5334_, 5, v_toPure_5327_);
    lean_closure_set(v___f_5334_, 6, v___f_5328_);
    v___x_5335_ = lean_apply_4(
        v_toBind_5325_,
        lean_box(0),
        lean_box(0),
        v_getEnv_5326_,
        v___f_5334_,
    );
    return v___x_5335_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens(
    mut v_m_5336_: *mut LeanObject,
    mut v_inst_5337_: *mut LeanObject,
    mut v_inst_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    v___x_5339_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_5337_, v_inst_5338_);
    return v___x_5339_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    v___x_5340_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5340_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    v___x_5341_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once), _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
    v___x_5342_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5342_, 0, v___x_5341_);
    return v___x_5342_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    v___x_5343_ = lean_box(1);
    v___x_5344_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
    v___x_5345_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
    v___x_5346_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5346_, 0, v___x_5345_);
    lean_ctor_set(v___x_5346_, 1, v___x_5344_);
    lean_ctor_set(v___x_5346_, 2, v___x_5343_);
    return v___x_5346_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(
    mut v_n_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
    mut v_toPure_5350_: *mut LeanObject,
    mut v_firsts_5351_: *mut LeanObject,
    mut v_____do__lift_5352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: u8 = 0;
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_5352_) == 0 {
                    v___x_5367_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3;
                    lean_inc(v_n_5348_);
                    v___x_5368_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v___x_5367_,
                        v_firsts_5351_,
                        v_n_5348_,
                    );
                    if lean_obj_tag(v___x_5368_) == 0 {
                        v___x_5369_ = 1;
                        lean_inc(v_n_5348_);
                        v___x_5370_ = l_Lean_Name_toString(v_n_5348_, v___x_5369_);
                        v___x_5371_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_5371_, 0, v___x_5370_);
                        v___y_5354_ = v___x_5371_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5372_ = lean_ctor_get(v___x_5368_, 0);
                        lean_inc(v_val_5372_);
                        lean_dec_ref_known(v___x_5368_, 1);
                        v_val_5365_ = v_val_5372_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_firsts_5351_);
                    v_val_5373_ = lean_ctor_get(v_____do__lift_5352_, 0);
                    lean_inc(v_val_5373_);
                    lean_dec_ref_known(v_____do__lift_5352_, 1);
                    v_val_5365_ = v_val_5373_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5355_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12,
                );
                v___x_5356_ = l_Lean_Expr_const___override(v_n_5348_, v___y_5349_);
                v___x_5357_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
                v___x_5358_ = lean_box(0);
                v___x_5359_ = 0;
                v___x_5360_ = l_Lean_MessageData_withExprHover(
                    v___y_5354_,
                    v___x_5356_,
                    v___x_5357_,
                    v___x_5358_,
                    v___x_5358_,
                    v___x_5358_,
                    v___x_5359_,
                );
                v___x_5361_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5361_, 0, v___x_5355_);
                lean_ctor_set(v___x_5361_, 1, v___x_5360_);
                v___x_5362_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5362_, 0, v___x_5361_);
                lean_ctor_set(v___x_5362_, 1, v___x_5355_);
                v___x_5363_ = lean_apply_2(v_toPure_5350_, lean_box(0), v___x_5362_);
                return v___x_5363_;
            }
            2 => {
                v___x_5366_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5366_, 0, v_val_5365_);
                v___y_5354_ = v___x_5366_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(
    mut v_n_5374_: *mut LeanObject,
    mut v_toPure_5375_: *mut LeanObject,
    mut v_firsts_5376_: *mut LeanObject,
    mut v_inst_5377_: *mut LeanObject,
    mut v_inst_5378_: *mut LeanObject,
    mut v_toBind_5379_: *mut LeanObject,
    mut v___x_5380_: *mut LeanObject,
    mut v___x_5381_: *mut LeanObject,
    mut v___f_5382_: *mut LeanObject,
    mut v_env_5383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5389_ = l_Lean_Environment_constants(v_env_5383_);
                lean_inc(v_n_5374_);
                v___x_5390_ = l_Lean_SMap_find_x3f_x27___redArg(
                    v___x_5380_,
                    v___x_5381_,
                    v___x_5389_,
                    v_n_5374_,
                );
                lean_dec_ref(v___x_5389_);
                if lean_obj_tag(v___x_5390_) == 0 {
                    lean_dec_ref(v___f_5382_);
                    v___x_5391_ = lean_box(0);
                    v___y_5385_ = v___x_5391_;
                    state = 1;
                    continue;
                } else {
                    v_val_5392_ = lean_ctor_get(v___x_5390_, 0);
                    lean_inc(v_val_5392_);
                    lean_dec_ref_known(v___x_5390_, 1);
                    v___x_5393_ = l_Lean_ConstantInfo_levelParams(v_val_5392_);
                    lean_dec(v_val_5392_);
                    v___x_5394_ = lean_box(0);
                    v___x_5395_ = l_List_mapTR_loop___redArg(v___f_5382_, v___x_5393_, v___x_5394_);
                    v___y_5385_ = v___x_5395_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_n_5374_);
                v___f_5386_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0 as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___f_5386_, 0, v_n_5374_);
                lean_closure_set(v___f_5386_, 1, v___y_5385_);
                lean_closure_set(v___f_5386_, 2, v_toPure_5375_);
                lean_closure_set(v___f_5386_, 3, v_firsts_5376_);
                v___x_5387_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(
                    v_inst_5377_,
                    v_inst_5378_,
                    v_n_5374_,
                );
                v___x_5388_ = lean_apply_4(
                    v_toBind_5379_,
                    lean_box(0),
                    lean_box(0),
                    v___x_5387_,
                    v___f_5386_,
                );
                return v___x_5388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(
    mut v_inst_5397_: *mut LeanObject,
    mut v_inst_5398_: *mut LeanObject,
    mut v_firsts_5399_: *mut LeanObject,
    mut v_n_5400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5401_ = lean_ctor_get(v_inst_5397_, 0);
    v_toBind_5402_ = lean_ctor_get(v_inst_5397_, 1);
    lean_inc_n(v_toBind_5402_, 2);
    v_getEnv_5403_ = lean_ctor_get(v_inst_5398_, 0);
    lean_inc(v_getEnv_5403_);
    v_toPure_5404_ = lean_ctor_get(v_toApplicative_5401_, 1);
    lean_inc(v_toPure_5404_);
    v___f_5405_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0;
    v___x_5406_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3;
    v___x_5407_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4;
    v___f_5408_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1
            as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_5408_, 0, v_n_5400_);
    lean_closure_set(v___f_5408_, 1, v_toPure_5404_);
    lean_closure_set(v___f_5408_, 2, v_firsts_5399_);
    lean_closure_set(v___f_5408_, 3, v_inst_5397_);
    lean_closure_set(v___f_5408_, 4, v_inst_5398_);
    lean_closure_set(v___f_5408_, 5, v_toBind_5402_);
    lean_closure_set(v___f_5408_, 6, v___x_5406_);
    lean_closure_set(v___f_5408_, 7, v___x_5407_);
    lean_closure_set(v___f_5408_, 8, v___f_5405_);
    v___x_5409_ = lean_apply_4(
        v_toBind_5402_,
        lean_box(0),
        lean_box(0),
        v_getEnv_5403_,
        v___f_5408_,
    );
    return v___x_5409_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(
    mut v_m_5410_: *mut LeanObject,
    mut v_inst_5411_: *mut LeanObject,
    mut v_inst_5412_: *mut LeanObject,
    mut v_firsts_5413_: *mut LeanObject,
    mut v_n_5414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    v___x_5415_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(
        v_inst_5411_,
        v_inst_5412_,
        v_firsts_5413_,
        v_n_5414_,
    );
    return v___x_5415_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(
    mut v_s_5418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    v___x_5419_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0;
    return v___x_5419_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(
    mut v_s_5420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5421_: *mut LeanObject = core::ptr::null_mut();
    v_res_5421_ =
        l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(
            v_s_5420_,
        );
    lean_dec_ref(v_s_5420_);
    return v_res_5421_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(
    mut v___x_5422_: u8,
    mut v_x1_5423_: *mut LeanObject,
    mut v_x2_5424_: *mut LeanObject,
) -> u8 {
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: u8 = 0;
    v___x_5425_ = l_Lean_Name_toString(v_x1_5423_, v___x_5422_);
    v___x_5426_ = l_Lean_Name_toString(v_x2_5424_, v___x_5422_);
    v___x_5427_ = lean_string_dec_lt(v___x_5425_, v___x_5426_);
    lean_dec_ref(v___x_5426_);
    lean_dec_ref(v___x_5425_);
    return v___x_5427_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(
    mut v___x_5428_: *mut LeanObject,
    mut v_x1_5429_: *mut LeanObject,
    mut v_x2_5430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_17024__boxed_5431_: u8 = 0;
    let mut v_res_5432_: u8 = 0;
    let mut v_r_5433_: *mut LeanObject = core::ptr::null_mut();
    v___x_17024__boxed_5431_ = (lean_unbox(v___x_5428_) as u8);
    v_res_5432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_17024__boxed_5431_, v_x1_5429_, v_x2_5430_);
    v_r_5433_ = lean_box((v_res_5432_) as usize);
    return v_r_5433_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(
    mut v_hi_5434_: *mut LeanObject,
    mut v_pivot_5435_: *mut LeanObject,
    mut v_as_5436_: *mut LeanObject,
    mut v_i_5437_: *mut LeanObject,
    mut v_k_5438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5439_: u8 = 0;
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: u8 = 0;
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5439_ = lean_nat_dec_lt(v_k_5438_, v_hi_5434_);
                if v___x_5439_ == 0 {
                    lean_dec(v_k_5438_);
                    lean_dec(v_pivot_5435_);
                    v___x_5440_ = lean_array_fswap(v_as_5436_, v_i_5437_, v_hi_5434_);
                    v___x_5441_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5441_, 0, v_i_5437_);
                    lean_ctor_set(v___x_5441_, 1, v___x_5440_);
                    return v___x_5441_;
                } else {
                    v___x_5442_ = lean_array_fget_borrowed(v_as_5436_, v_k_5438_);
                    lean_inc(v___x_5442_);
                    v___x_5443_ = l_Lean_Name_toString(v___x_5442_, v___x_5439_);
                    lean_inc(v_pivot_5435_);
                    v___x_5444_ = l_Lean_Name_toString(v_pivot_5435_, v___x_5439_);
                    v___x_5445_ = lean_string_dec_lt(v___x_5443_, v___x_5444_);
                    lean_dec_ref(v___x_5444_);
                    lean_dec_ref(v___x_5443_);
                    if v___x_5445_ == 0 {
                        v___x_5446_ = lean_unsigned_to_nat(1);
                        v___x_5447_ = lean_nat_add(v_k_5438_, v___x_5446_);
                        lean_dec(v_k_5438_);
                        v_k_5438_ = v___x_5447_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5449_ = lean_array_fswap(v_as_5436_, v_i_5437_, v_k_5438_);
                        v___x_5450_ = lean_unsigned_to_nat(1);
                        v___x_5451_ = lean_nat_add(v_i_5437_, v___x_5450_);
                        lean_dec(v_i_5437_);
                        v___x_5452_ = lean_nat_add(v_k_5438_, v___x_5450_);
                        lean_dec(v_k_5438_);
                        v_as_5436_ = v___x_5449_;
                        v_i_5437_ = v___x_5451_;
                        v_k_5438_ = v___x_5452_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(
    mut v_hi_5454_: *mut LeanObject,
    mut v_pivot_5455_: *mut LeanObject,
    mut v_as_5456_: *mut LeanObject,
    mut v_i_5457_: *mut LeanObject,
    mut v_k_5458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5459_: *mut LeanObject = core::ptr::null_mut();
    v_res_5459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_5454_, v_pivot_5455_, v_as_5456_, v_i_5457_, v_k_5458_);
    lean_dec(v_hi_5454_);
    return v_res_5459_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(
    mut v_n_5460_: *mut LeanObject,
    mut v_as_5461_: *mut LeanObject,
    mut v_lo_5462_: *mut LeanObject,
    mut v_hi_5463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: u8 = 0;
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: u8 = 0;
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: u8 = 0;
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: u8 = 0;
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5475_ = lean_nat_dec_lt(v_lo_5462_, v_hi_5463_);
                if v___x_5475_ == 0 {
                    lean_dec(v_lo_5462_);
                    return v_as_5461_;
                } else {
                    v___x_5476_ = lean_nat_add(v_lo_5462_, v_hi_5463_);
                    v___x_5477_ = lean_unsigned_to_nat(1);
                    v_mid_5478_ = lean_nat_shiftr(v___x_5476_, v___x_5477_);
                    lean_dec(v___x_5476_);
                    v___x_5491_ = lean_array_fget_borrowed(v_as_5461_, v_mid_5478_);
                    v___x_5492_ = lean_array_fget_borrowed(v_as_5461_, v_lo_5462_);
                    lean_inc(v___x_5492_);
                    lean_inc(v___x_5491_);
                    v___x_5493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_5475_, v___x_5491_, v___x_5492_);
                    if v___x_5493_ == 0 {
                        v___y_5486_ = v_as_5461_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5494_ = lean_array_fswap(v_as_5461_, v_lo_5462_, v_mid_5478_);
                        v___y_5486_ = v___x_5494_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_5466_ = lean_array_fget(v___y_5465_, v_hi_5463_);
                lean_inc_n(v_lo_5462_, 2);
                v___x_5467_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_5463_, v_pivot_5466_, v___y_5465_, v_lo_5462_, v_lo_5462_);
                v_fst_5468_ = lean_ctor_get(v___x_5467_, 0);
                lean_inc(v_fst_5468_);
                v_snd_5469_ = lean_ctor_get(v___x_5467_, 1);
                lean_inc(v_snd_5469_);
                lean_dec_ref(v___x_5467_);
                v___x_5470_ = lean_nat_dec_le(v_hi_5463_, v_fst_5468_);
                if v___x_5470_ == 0 {
                    v___x_5471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_5460_, v_snd_5469_, v_lo_5462_, v_fst_5468_);
                    v___x_5472_ = lean_unsigned_to_nat(1);
                    v___x_5473_ = lean_nat_add(v_fst_5468_, v___x_5472_);
                    lean_dec(v_fst_5468_);
                    v_as_5461_ = v___x_5471_;
                    v_lo_5462_ = v___x_5473_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_5468_);
                    lean_dec(v_lo_5462_);
                    return v_snd_5469_;
                }
            }
            2 => {
                v___x_5481_ = lean_array_fget_borrowed(v___y_5480_, v_mid_5478_);
                v___x_5482_ = lean_array_fget_borrowed(v___y_5480_, v_hi_5463_);
                lean_inc(v___x_5482_);
                lean_inc(v___x_5481_);
                v___x_5483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_5475_, v___x_5481_, v___x_5482_);
                if v___x_5483_ == 0 {
                    lean_dec(v_mid_5478_);
                    v___y_5465_ = v___y_5480_;
                    state = 1;
                    continue;
                } else {
                    v___x_5484_ = lean_array_fswap(v___y_5480_, v_mid_5478_, v_hi_5463_);
                    lean_dec(v_mid_5478_);
                    v___y_5465_ = v___x_5484_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5487_ = lean_array_fget_borrowed(v___y_5486_, v_hi_5463_);
                v___x_5488_ = lean_array_fget_borrowed(v___y_5486_, v_lo_5462_);
                lean_inc(v___x_5488_);
                lean_inc(v___x_5487_);
                v___x_5489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_5475_, v___x_5487_, v___x_5488_);
                if v___x_5489_ == 0 {
                    v___y_5480_ = v___y_5486_;
                    state = 2;
                    continue;
                } else {
                    v___x_5490_ = lean_array_fswap(v___y_5486_, v_lo_5462_, v_hi_5463_);
                    v___y_5480_ = v___x_5490_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(
    mut v_n_5495_: *mut LeanObject,
    mut v_as_5496_: *mut LeanObject,
    mut v_lo_5497_: *mut LeanObject,
    mut v_hi_5498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5499_: *mut LeanObject = core::ptr::null_mut();
    v_res_5499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_5495_, v_as_5496_, v_lo_5497_, v_hi_5498_);
    lean_dec(v_hi_5498_);
    lean_dec(v_n_5495_);
    return v_res_5499_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(
    mut v_init_5500_: *mut LeanObject,
    mut v_x_5501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5501_) == 0 {
                    v_k_5502_ = lean_ctor_get(v_x_5501_, 1);
                    lean_inc(v_k_5502_);
                    v_l_5503_ = lean_ctor_get(v_x_5501_, 3);
                    lean_inc(v_l_5503_);
                    v_r_5504_ = lean_ctor_get(v_x_5501_, 4);
                    lean_inc(v_r_5504_);
                    lean_dec_ref_known(v_x_5501_, 5);
                    v___x_5505_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_5500_, v_l_5503_);
                    v___x_5506_ = lean_array_push(v___x_5505_, v_k_5502_);
                    v_init_5500_ = v___x_5506_;
                    v_x_5501_ = v_r_5504_;
                    state = 0;
                    continue;
                } else {
                    return v_init_5500_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(
    mut v_a_5508_: *mut LeanObject,
    mut v_a_5509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5508_) == 0 {
                    v___x_5510_ = l_List_reverse___redArg(v_a_5509_);
                    return v___x_5510_;
                } else {
                    v_head_5511_ = lean_ctor_get(v_a_5508_, 0);
                    v_tail_5512_ = lean_ctor_get(v_a_5508_, 1);
                    v_isSharedCheck_5521_ = (!lean_is_exclusive(v_a_5508_)) as u8;
                    if v_isSharedCheck_5521_ == 0 {
                        v___x_5514_ = v_a_5508_;
                        v_isShared_5515_ = v_isSharedCheck_5521_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5512_);
                        lean_inc(v_head_5511_);
                        lean_dec(v_a_5508_);
                        v___x_5514_ = lean_box(0);
                        v_isShared_5515_ = v_isSharedCheck_5521_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5516_ = l_Lean_Level_param___override(v_head_5511_);
                if v_isShared_5515_ == 0 {
                    lean_ctor_set(v___x_5514_, 1, v_a_5509_);
                    lean_ctor_set(v___x_5514_, 0, v___x_5516_);
                    v___x_5518_ = v___x_5514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5516_);
                    lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_a_5509_);
                    v___x_5518_ = v_reuseFailAlloc_5520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5508_ = v_tail_5512_;
                v_a_5509_ = v___x_5518_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(
    mut v_x1_5522_: *mut LeanObject,
    mut v_x2_5523_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    v_fst_5524_ = lean_ctor_get(v_x1_5522_, 0);
    v_fst_5525_ = lean_ctor_get(v_x2_5523_, 0);
    v___x_5526_ = l_Lean_Name_quickLt(v_fst_5524_, v_fst_5525_);
    return v___x_5526_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(
    mut v_x1_5527_: *mut LeanObject,
    mut v_x2_5528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5529_: u8 = 0;
    let mut v_r_5530_: *mut LeanObject = core::ptr::null_mut();
    v_res_5529_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_5527_, v_x2_5528_);
    lean_dec_ref(v_x2_5528_);
    lean_dec_ref(v_x1_5527_);
    v_r_5530_ = lean_box((v_res_5529_) as usize);
    return v_r_5530_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(
    mut v_as_5531_: *mut LeanObject,
    mut v_k_5532_: *mut LeanObject,
    mut v_x_5533_: *mut LeanObject,
    mut v_x_5534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: u8 = 0;
    let mut v___x_5540_: u8 = 0;
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: u8 = 0;
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: u8 = 0;
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: u8 = 0;
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5535_ = lean_nat_add(v_x_5533_, v_x_5534_);
                v___x_5536_ = lean_unsigned_to_nat(1);
                v_m_5537_ = lean_nat_shiftr(v___x_5535_, v___x_5536_);
                lean_dec(v___x_5535_);
                v_a_5538_ = lean_array_fget_borrowed(v_as_5531_, v_m_5537_);
                v___x_5539_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_5538_, v_k_5532_);
                if v___x_5539_ == 0 {
                    lean_dec(v_x_5534_);
                    v___x_5540_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_5532_, v_a_5538_);
                    if v___x_5540_ == 0 {
                        lean_dec(v_m_5537_);
                        lean_dec(v_x_5533_);
                        lean_inc(v_a_5538_);
                        v___x_5541_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5541_, 0, v_a_5538_);
                        return v___x_5541_;
                    } else {
                        v___x_5542_ = lean_unsigned_to_nat(0);
                        v___x_5543_ = lean_nat_dec_eq(v_m_5537_, v___x_5542_);
                        if v___x_5543_ == 0 {
                            v___x_5544_ = lean_nat_sub(v_m_5537_, v___x_5536_);
                            lean_dec(v_m_5537_);
                            v___x_5545_ = lean_nat_dec_lt(v___x_5544_, v_x_5533_);
                            if v___x_5545_ == 0 {
                                v_x_5534_ = v___x_5544_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_5544_);
                                lean_dec(v_x_5533_);
                                v___x_5547_ = lean_box(0);
                                return v___x_5547_;
                            }
                        } else {
                            lean_dec(v_m_5537_);
                            lean_dec(v_x_5533_);
                            v___x_5548_ = lean_box(0);
                            return v___x_5548_;
                        }
                    }
                } else {
                    lean_dec(v_x_5533_);
                    v___x_5549_ = lean_nat_add(v_m_5537_, v___x_5536_);
                    lean_dec(v_m_5537_);
                    v___x_5550_ = lean_nat_dec_le(v___x_5549_, v_x_5534_);
                    if v___x_5550_ == 0 {
                        lean_dec(v___x_5549_);
                        lean_dec(v_x_5534_);
                        v___x_5551_ = lean_box(0);
                        return v___x_5551_;
                    } else {
                        v_x_5533_ = v___x_5549_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(
    mut v_as_5553_: *mut LeanObject,
    mut v_k_5554_: *mut LeanObject,
    mut v_x_5555_: *mut LeanObject,
    mut v_x_5556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5557_: *mut LeanObject = core::ptr::null_mut();
    v_res_5557_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_5553_, v_k_5554_, v_x_5555_, v_x_5556_);
    lean_dec_ref(v_k_5554_);
    lean_dec_ref(v_as_5553_);
    return v_res_5557_;
}
pub unsafe fn l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(
    mut v_tac_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5579_: u8 = 0;
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: u8 = 0;
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: u8 = 0;
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: u8 = 0;
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v_snd_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut v_isSharedCheck_5604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5562_ = lean_st_ref_get(v___y_5560_);
                v_env_5566_ = lean_ctor_get(v___x_5562_, 0);
                lean_inc_ref(v_env_5566_);
                lean_dec(v___x_5562_);
                v___x_5567_ = lean_box(1);
                v___x_5568_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5566_, v_tac_5559_);
                if lean_obj_tag(v___x_5568_) == 0 {
                    v___x_5569_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
                    v_toEnvExtension_5570_ = lean_ctor_get(v___x_5569_, 0);
                    v_asyncMode_5571_ = lean_ctor_get(v_toEnvExtension_5570_, 2);
                    v___x_5572_ = lean_box(0);
                    v___x_5573_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_5567_,
                        v___x_5569_,
                        v_env_5566_,
                        v_asyncMode_5571_,
                        v___x_5572_,
                    );
                    v___x_5574_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5573_, v_tac_5559_);
                    lean_dec(v_tac_5559_);
                    lean_dec(v___x_5573_);
                    v___x_5575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5575_, 0, v___x_5574_);
                    return v___x_5575_;
                } else {
                    v_val_5576_ = lean_ctor_get(v___x_5568_, 0);
                    v_isSharedCheck_5604_ = (!lean_is_exclusive(v___x_5568_)) as u8;
                    if v_isSharedCheck_5604_ == 0 {
                        v___x_5578_ = v___x_5568_;
                        v_isShared_5579_ = v_isSharedCheck_5604_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_5576_);
                        lean_dec(v___x_5568_);
                        v___x_5578_ = lean_box(0);
                        v_isShared_5579_ = v_isSharedCheck_5604_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5564_ = lean_box(0);
                v___x_5565_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5565_, 0, v___x_5564_);
                return v___x_5565_;
            }
            2 => {
                v___x_5580_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
                v___x_5581_ = 0;
                v___x_5582_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_5567_,
                    v___x_5580_,
                    v_env_5566_,
                    v_val_5576_,
                    v___x_5581_,
                );
                lean_dec(v_val_5576_);
                lean_dec_ref(v_env_5566_);
                v___x_5583_ = lean_unsigned_to_nat(0);
                v___x_5584_ = lean_array_get_size(v___x_5582_);
                v___x_5585_ = lean_nat_dec_lt(v___x_5583_, v___x_5584_);
                if v___x_5585_ == 0 {
                    lean_dec_ref(v___x_5582_);
                    lean_del_object(v___x_5578_);
                    lean_dec(v_tac_5559_);
                    state = 1;
                    continue;
                } else {
                    v___x_5586_ = lean_unsigned_to_nat(1);
                    v___x_5587_ = lean_nat_sub(v___x_5584_, v___x_5586_);
                    v___x_5588_ = lean_nat_dec_le(v___x_5583_, v___x_5587_);
                    if v___x_5588_ == 0 {
                        lean_dec(v___x_5587_);
                        lean_dec_ref(v___x_5582_);
                        lean_del_object(v___x_5578_);
                        lean_dec(v_tac_5559_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5589_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0;
                        v___x_5590_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5590_, 0, v_tac_5559_);
                        lean_ctor_set(v___x_5590_, 1, v___x_5589_);
                        v___x_5591_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_5582_, v___x_5590_, v___x_5583_, v___x_5587_);
                        lean_dec_ref_known(v___x_5590_, 2);
                        lean_dec_ref(v___x_5582_);
                        if lean_obj_tag(v___x_5591_) == 0 {
                            lean_del_object(v___x_5578_);
                            state = 1;
                            continue;
                        } else {
                            v_val_5592_ = lean_ctor_get(v___x_5591_, 0);
                            v_isSharedCheck_5603_ = (!lean_is_exclusive(v___x_5591_)) as u8;
                            if v_isSharedCheck_5603_ == 0 {
                                v___x_5594_ = v___x_5591_;
                                v_isShared_5595_ = v_isSharedCheck_5603_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_val_5592_);
                                lean_dec(v___x_5591_);
                                v___x_5594_ = lean_box(0);
                                v_isShared_5595_ = v_isSharedCheck_5603_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v_snd_5596_ = lean_ctor_get(v_val_5592_, 1);
                lean_inc(v_snd_5596_);
                lean_dec(v_val_5592_);
                if v_isShared_5595_ == 0 {
                    lean_ctor_set(v___x_5594_, 0, v_snd_5596_);
                    v___x_5598_ = v___x_5594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_snd_5596_);
                    v___x_5598_ = v_reuseFailAlloc_5602_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5579_ == 0 {
                    lean_ctor_set_tag(v___x_5578_, 0);
                    lean_ctor_set(v___x_5578_, 0, v___x_5598_);
                    v___x_5600_ = v___x_5578_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5598_);
                    v___x_5600_ = v_reuseFailAlloc_5601_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(
    mut v_tac_5605_: *mut LeanObject,
    mut v___y_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5608_: *mut LeanObject = core::ptr::null_mut();
    v_res_5608_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_5605_, v___y_5606_);
    lean_dec(v___y_5606_);
    return v_res_5608_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(
    mut v_t_5609_: *mut LeanObject,
    mut v_k_5610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: u8 = 0;
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5609_) == 0 {
                    v_k_5611_ = lean_ctor_get(v_t_5609_, 1);
                    v_v_5612_ = lean_ctor_get(v_t_5609_, 2);
                    v_l_5613_ = lean_ctor_get(v_t_5609_, 3);
                    v_r_5614_ = lean_ctor_get(v_t_5609_, 4);
                    v___x_5615_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5610_, v_k_5611_);
                    match v___x_5615_ {
                        0 => {
                            v_t_5609_ = v_l_5613_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_5612_);
                            v___x_5617_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5617_, 0, v_v_5612_);
                            return v___x_5617_;
                        }
                        _ => {
                            v_t_5609_ = v_r_5614_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5619_ = lean_box(0);
                    return v___x_5619_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(
    mut v_t_5620_: *mut LeanObject,
    mut v_k_5621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5622_: *mut LeanObject = core::ptr::null_mut();
    v_res_5622_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_5620_, v_k_5621_);
    lean_dec(v_k_5621_);
    lean_dec(v_t_5620_);
    return v_res_5622_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(
    mut v_a_5623_: *mut LeanObject,
    mut v_x_5624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5624_) == 0 {
                    v___x_5625_ = lean_box(0);
                    return v___x_5625_;
                } else {
                    v_key_5626_ = lean_ctor_get(v_x_5624_, 0);
                    v_value_5627_ = lean_ctor_get(v_x_5624_, 1);
                    v_tail_5628_ = lean_ctor_get(v_x_5624_, 2);
                    v___x_5629_ = lean_name_eq(v_key_5626_, v_a_5623_);
                    if v___x_5629_ == 0 {
                        v_x_5624_ = v_tail_5628_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_5627_);
                        v___x_5631_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5631_, 0, v_value_5627_);
                        return v___x_5631_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(
    mut v_a_5632_: *mut LeanObject,
    mut v_x_5633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5634_: *mut LeanObject = core::ptr::null_mut();
    v_res_5634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_5632_, v_x_5633_);
    lean_dec(v_x_5633_);
    lean_dec(v_a_5632_);
    return v_res_5634_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(
    mut v_m_5635_: *mut LeanObject,
    mut v_a_5636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: u64 = 0;
    let mut v___x_5641_: u64 = 0;
    let mut v___x_5642_: u64 = 0;
    let mut v_fold_5643_: u64 = 0;
    let mut v___x_5644_: u64 = 0;
    let mut v___x_5645_: u64 = 0;
    let mut v___x_5646_: u64 = 0;
    let mut v___x_5647_: usize = 0;
    let mut v___x_5648_: usize = 0;
    let mut v___x_5649_: usize = 0;
    let mut v___x_5650_: usize = 0;
    let mut v___x_5651_: usize = 0;
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: u64 = 0;
    let mut v_hash_5655_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5637_ = lean_ctor_get(v_m_5635_, 1);
                v___x_5638_ = lean_array_get_size(v_buckets_5637_);
                if lean_obj_tag(v_a_5636_) == 0 {
                    v___x_5654_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
                    v___y_5640_ = v___x_5654_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5655_ = lean_ctor_get_uint64(
                        v_a_5636_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_5640_ = v_hash_5655_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5641_ = 32u64;
                v___x_5642_ = lean_uint64_shift_right(v___y_5640_, v___x_5641_);
                v_fold_5643_ = lean_uint64_xor(v___y_5640_, v___x_5642_);
                v___x_5644_ = 16u64;
                v___x_5645_ = lean_uint64_shift_right(v_fold_5643_, v___x_5644_);
                v___x_5646_ = lean_uint64_xor(v_fold_5643_, v___x_5645_);
                v___x_5647_ = lean_uint64_to_usize(v___x_5646_);
                v___x_5648_ = lean_usize_of_nat(v___x_5638_);
                v___x_5649_ = 1usize;
                v___x_5650_ = lean_usize_sub(v___x_5648_, v___x_5649_);
                v___x_5651_ = lean_usize_land(v___x_5647_, v___x_5650_);
                v___x_5652_ = lean_array_uget_borrowed(v_buckets_5637_, v___x_5651_);
                v___x_5653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_5636_, v___x_5652_);
                return v___x_5653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(
    mut v_m_5656_: *mut LeanObject,
    mut v_a_5657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5658_: *mut LeanObject = core::ptr::null_mut();
    v_res_5658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_5656_, v_a_5657_);
    lean_dec(v_a_5657_);
    lean_dec_ref(v_m_5656_);
    return v_res_5658_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(
    mut v_keys_5659_: *mut LeanObject,
    mut v_vals_5660_: *mut LeanObject,
    mut v_i_5661_: *mut LeanObject,
    mut v_k_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: u8 = 0;
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5663_ = lean_array_get_size(v_keys_5659_);
                v___x_5664_ = lean_nat_dec_lt(v_i_5661_, v___x_5663_);
                if v___x_5664_ == 0 {
                    lean_dec(v_i_5661_);
                    v___x_5665_ = lean_box(0);
                    return v___x_5665_;
                } else {
                    v_k_x27_5666_ = lean_array_fget_borrowed(v_keys_5659_, v_i_5661_);
                    v___x_5667_ = lean_name_eq(v_k_5662_, v_k_x27_5666_);
                    if v___x_5667_ == 0 {
                        v___x_5668_ = lean_unsigned_to_nat(1);
                        v___x_5669_ = lean_nat_add(v_i_5661_, v___x_5668_);
                        lean_dec(v_i_5661_);
                        v_i_5661_ = v___x_5669_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5671_ = lean_array_fget_borrowed(v_vals_5660_, v_i_5661_);
                        lean_dec(v_i_5661_);
                        lean_inc(v___x_5671_);
                        v___x_5672_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5672_, 0, v___x_5671_);
                        return v___x_5672_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(
    mut v_keys_5673_: *mut LeanObject,
    mut v_vals_5674_: *mut LeanObject,
    mut v_i_5675_: *mut LeanObject,
    mut v_k_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5677_: *mut LeanObject = core::ptr::null_mut();
    v_res_5677_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_5673_, v_vals_5674_, v_i_5675_, v_k_5676_);
    lean_dec(v_k_5676_);
    lean_dec_ref(v_vals_5674_);
    lean_dec_ref(v_keys_5673_);
    return v_res_5677_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(
    mut v_x_5678_: *mut LeanObject,
    mut v_x_5679_: usize,
    mut v_x_5680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: usize = 0;
    let mut v___x_5684_: usize = 0;
    let mut v___x_5685_: usize = 0;
    let mut v_j_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: usize = 0;
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5678_) == 0 {
                    v_es_5681_ = lean_ctor_get(v_x_5678_, 0);
                    v___x_5682_ = lean_box(2);
                    v___x_5683_ = 5usize;
                    v___x_5684_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
                    v___x_5685_ = lean_usize_land(v_x_5679_, v___x_5684_);
                    v_j_5686_ = lean_usize_to_nat(v___x_5685_);
                    v___x_5687_ = lean_array_get_borrowed(v___x_5682_, v_es_5681_, v_j_5686_);
                    lean_dec(v_j_5686_);
                    match lean_obj_tag(v___x_5687_) {
                        0 => {
                            v_key_5688_ = lean_ctor_get(v___x_5687_, 0);
                            v_val_5689_ = lean_ctor_get(v___x_5687_, 1);
                            v___x_5690_ = lean_name_eq(v_x_5680_, v_key_5688_);
                            if v___x_5690_ == 0 {
                                v___x_5691_ = lean_box(0);
                                return v___x_5691_;
                            } else {
                                lean_inc(v_val_5689_);
                                v___x_5692_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_5692_, 0, v_val_5689_);
                                return v___x_5692_;
                            }
                        }
                        1 => {
                            v_node_5693_ = lean_ctor_get(v___x_5687_, 0);
                            v___x_5694_ = lean_usize_shift_right(v_x_5679_, v___x_5683_);
                            v_x_5678_ = v_node_5693_;
                            v_x_5679_ = v___x_5694_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5696_ = lean_box(0);
                            return v___x_5696_;
                        }
                    }
                } else {
                    v_ks_5697_ = lean_ctor_get(v_x_5678_, 0);
                    v_vs_5698_ = lean_ctor_get(v_x_5678_, 1);
                    v___x_5699_ = lean_unsigned_to_nat(0);
                    v___x_5700_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_5697_, v_vs_5698_, v___x_5699_, v_x_5680_);
                    return v___x_5700_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_x_5701_: *mut LeanObject,
    mut v_x_5702_: *mut LeanObject,
    mut v_x_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17406__boxed_5704_: usize = 0;
    let mut v_res_5705_: *mut LeanObject = core::ptr::null_mut();
    v_x_17406__boxed_5704_ = lean_unbox_usize(v_x_5702_);
    lean_dec(v_x_5702_);
    v_res_5705_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_5701_, v_x_17406__boxed_5704_, v_x_5703_);
    lean_dec(v_x_5703_);
    lean_dec_ref(v_x_5701_);
    return v_res_5705_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(
    mut v_x_5706_: *mut LeanObject,
    mut v_x_5707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5709_: u64 = 0;
    let mut v___x_5710_: usize = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: u64 = 0;
    let mut v_hash_5713_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5707_) == 0 {
                    v___x_5712_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
                    v___y_5709_ = v___x_5712_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5713_ = lean_ctor_get_uint64(
                        v_x_5707_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_5709_ = v_hash_5713_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5710_ = lean_uint64_to_usize(v___y_5709_);
                v___x_5711_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_5706_, v___x_5710_, v_x_5707_);
                return v___x_5711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(
    mut v_x_5714_: *mut LeanObject,
    mut v_x_5715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5716_: *mut LeanObject = core::ptr::null_mut();
    v_res_5716_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_5714_, v_x_5715_);
    lean_dec(v_x_5715_);
    lean_dec_ref(v_x_5714_);
    return v_res_5716_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(
    mut v_x_5717_: *mut LeanObject,
    mut v_x_5718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_5719_: u8 = 0;
    v_stage_u2081_5719_ = lean_ctor_get_uint8(
        v_x_5717_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_5719_ == 0 {
        let mut v_map_u2081_5720_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_5721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_5720_ = lean_ctor_get(v_x_5717_, 0);
        v_map_u2082_5721_ = lean_ctor_get(v_x_5717_, 1);
        v___x_5722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_5720_, v_x_5718_);
        if lean_obj_tag(v___x_5722_) == 0 {
            let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
            v___x_5723_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_5721_, v_x_5718_);
            return v___x_5723_;
        } else {
            return v___x_5722_;
        }
    } else {
        let mut v_map_u2081_5724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_5724_ = lean_ctor_get(v_x_5717_, 0);
        v___x_5725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_5724_, v_x_5718_);
        return v___x_5725_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(
    mut v_x_5726_: *mut LeanObject,
    mut v_x_5727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5728_: *mut LeanObject = core::ptr::null_mut();
    v_res_5728_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_5726_, v_x_5727_);
    lean_dec(v_x_5727_);
    lean_dec_ref(v_x_5726_);
    return v_res_5728_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(
    mut v_firsts_5729_: *mut LeanObject,
    mut v_n_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
    mut v___y_5732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: u8 = 0;
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5768_: u8 = 0;
    let mut v_env_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5752_ = lean_st_ref_get(v___y_5732_);
                v_env_5769_ = lean_ctor_get(v___x_5752_, 0);
                lean_inc_ref(v_env_5769_);
                lean_dec(v___x_5752_);
                v___x_5770_ = l_Lean_Environment_constants(v_env_5769_);
                v___x_5771_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_5770_, v_n_5730_);
                lean_dec_ref(v___x_5770_);
                if lean_obj_tag(v___x_5771_) == 0 {
                    v___x_5772_ = lean_box(0);
                    v___y_5754_ = v___x_5772_;
                    state = 3;
                    continue;
                } else {
                    v_val_5773_ = lean_ctor_get(v___x_5771_, 0);
                    lean_inc(v_val_5773_);
                    lean_dec_ref_known(v___x_5771_, 1);
                    v___x_5774_ = l_Lean_ConstantInfo_levelParams(v_val_5773_);
                    lean_dec(v_val_5773_);
                    v___x_5775_ = lean_box(0);
                    v___x_5776_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_5774_, v___x_5775_);
                    v___y_5754_ = v___x_5776_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_5737_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12,
                );
                v___x_5738_ = l_Lean_Expr_const___override(v_n_5730_, v___y_5735_);
                v___x_5739_ = lean_unsigned_to_nat(32);
                v___x_5740_ = lean_mk_empty_array_with_capacity(v___x_5739_);
                lean_dec_ref(v___x_5740_);
                v___x_5741_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
                v___x_5742_ = lean_box(0);
                v___x_5743_ = 0;
                v___x_5744_ = l_Lean_MessageData_withExprHover(
                    v___y_5736_,
                    v___x_5738_,
                    v___x_5741_,
                    v___x_5742_,
                    v___x_5742_,
                    v___x_5742_,
                    v___x_5743_,
                );
                v___x_5745_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5745_, 0, v___x_5737_);
                lean_ctor_set(v___x_5745_, 1, v___x_5744_);
                v___x_5746_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5746_, 0, v___x_5745_);
                lean_ctor_set(v___x_5746_, 1, v___x_5737_);
                v___x_5747_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5747_, 0, v___x_5746_);
                return v___x_5747_;
            }
            2 => {
                v___x_5751_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5751_, 0, v_val_5750_);
                v___y_5735_ = v___y_5749_;
                v___y_5736_ = v___x_5751_;
                state = 1;
                continue;
            }
            3 => {
                lean_inc(v_n_5730_);
                v___x_5755_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_5730_, v___y_5732_);
                v_a_5756_ = lean_ctor_get(v___x_5755_, 0);
                v_isSharedCheck_5768_ = (!lean_is_exclusive(v___x_5755_)) as u8;
                if v_isSharedCheck_5768_ == 0 {
                    v___x_5758_ = v___x_5755_;
                    v_isShared_5759_ = v_isSharedCheck_5768_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_5756_);
                    lean_dec(v___x_5755_);
                    v___x_5758_ = lean_box(0);
                    v_isShared_5759_ = v_isSharedCheck_5768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if lean_obj_tag(v_a_5756_) == 0 {
                    v___x_5760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_5729_, v_n_5730_);
                    if lean_obj_tag(v___x_5760_) == 0 {
                        v___x_5761_ = 1;
                        lean_inc(v_n_5730_);
                        v___x_5762_ = l_Lean_Name_toString(v_n_5730_, v___x_5761_);
                        if v_isShared_5759_ == 0 {
                            lean_ctor_set_tag(v___x_5758_, 3);
                            lean_ctor_set(v___x_5758_, 0, v___x_5762_);
                            v___x_5764_ = v___x_5758_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_5765_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5762_);
                            v___x_5764_ = v_reuseFailAlloc_5765_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5758_);
                        v_val_5766_ = lean_ctor_get(v___x_5760_, 0);
                        lean_inc(v_val_5766_);
                        lean_dec_ref_known(v___x_5760_, 1);
                        v___y_5749_ = v___y_5754_;
                        v_val_5750_ = v_val_5766_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5758_);
                    v_val_5767_ = lean_ctor_get(v_a_5756_, 0);
                    lean_inc(v_val_5767_);
                    lean_dec_ref_known(v_a_5756_, 1);
                    v___y_5749_ = v___y_5754_;
                    v_val_5750_ = v_val_5767_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___y_5735_ = v___y_5754_;
                v___y_5736_ = v___x_5764_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(
    mut v_firsts_5777_: *mut LeanObject,
    mut v_n_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5782_: *mut LeanObject = core::ptr::null_mut();
    v_res_5782_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_5777_, v_n_5778_, v___y_5779_, v___y_5780_);
    lean_dec(v___y_5780_);
    lean_dec_ref(v___y_5779_);
    lean_dec(v_firsts_5777_);
    return v_res_5782_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(
    mut v_a_5783_: *mut LeanObject,
    mut v_x_5784_: *mut LeanObject,
    mut v_x_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5805_: u8 = 0;
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5809_: u8 = 0;
    let mut v_isSharedCheck_5810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5784_) == 0 {
                    v___x_5789_ = l_List_reverse___redArg(v_x_5785_);
                    v___x_5790_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5790_, 0, v___x_5789_);
                    return v___x_5790_;
                } else {
                    v_head_5791_ = lean_ctor_get(v_x_5784_, 0);
                    v_tail_5792_ = lean_ctor_get(v_x_5784_, 1);
                    v_isSharedCheck_5810_ = (!lean_is_exclusive(v_x_5784_)) as u8;
                    if v_isSharedCheck_5810_ == 0 {
                        v___x_5794_ = v_x_5784_;
                        v_isShared_5795_ = v_isSharedCheck_5810_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5792_);
                        lean_inc(v_head_5791_);
                        lean_dec(v_x_5784_);
                        v___x_5794_ = lean_box(0);
                        v_isShared_5795_ = v_isSharedCheck_5810_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5796_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_5783_, v_head_5791_, v___y_5786_, v___y_5787_);
                if lean_obj_tag(v___x_5796_) == 0 {
                    v_a_5797_ = lean_ctor_get(v___x_5796_, 0);
                    lean_inc(v_a_5797_);
                    lean_dec_ref_known(v___x_5796_, 1);
                    if v_isShared_5795_ == 0 {
                        lean_ctor_set(v___x_5794_, 1, v_x_5785_);
                        lean_ctor_set(v___x_5794_, 0, v_a_5797_);
                        v___x_5799_ = v___x_5794_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5801_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_a_5797_);
                        lean_ctor_set(v_reuseFailAlloc_5801_, 1, v_x_5785_);
                        v___x_5799_ = v_reuseFailAlloc_5801_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5794_);
                    lean_dec(v_tail_5792_);
                    lean_dec(v_x_5785_);
                    v_a_5802_ = lean_ctor_get(v___x_5796_, 0);
                    v_isSharedCheck_5809_ = (!lean_is_exclusive(v___x_5796_)) as u8;
                    if v_isSharedCheck_5809_ == 0 {
                        v___x_5804_ = v___x_5796_;
                        v_isShared_5805_ = v_isSharedCheck_5809_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5802_);
                        lean_dec(v___x_5796_);
                        v___x_5804_ = lean_box(0);
                        v_isShared_5805_ = v_isSharedCheck_5809_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_5784_ = v_tail_5792_;
                v_x_5785_ = v___x_5799_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5805_ == 0 {
                    v___x_5807_ = v___x_5804_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_a_5802_);
                    v___x_5807_ = v_reuseFailAlloc_5808_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(
    mut v_a_5811_: *mut LeanObject,
    mut v_x_5812_: *mut LeanObject,
    mut v_x_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5817_: *mut LeanObject = core::ptr::null_mut();
    v_res_5817_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(
        v_a_5811_,
        v_x_5812_,
        v_x_5813_,
        v___y_5814_,
        v___y_5815_,
    );
    lean_dec(v___y_5815_);
    lean_dec_ref(v___y_5814_);
    lean_dec(v_a_5811_);
    return v_res_5817_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(
    mut v_val_5818_: *mut LeanObject,
    mut v___x_5819_: *mut LeanObject,
    mut v___x_5820_: *mut LeanObject,
    mut v_a_5821_: *mut LeanObject,
    mut v_b_5822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v_startInclusive_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: u8 = 0;
    let mut v___x_5840_: u32 = 0;
    let mut v___x_5841_: u32 = 0;
    let mut v___x_5842_: u8 = 0;
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5821_) == 0 {
                    v_currPos_5831_ = lean_ctor_get(v_a_5821_, 0);
                    v_searcher_5832_ = lean_ctor_get(v_a_5821_, 1);
                    v_isSharedCheck_5858_ = (!lean_is_exclusive(v_a_5821_)) as u8;
                    if v_isSharedCheck_5858_ == 0 {
                        v___x_5834_ = v_a_5821_;
                        v_isShared_5835_ = v_isSharedCheck_5858_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_5832_);
                        lean_inc(v_currPos_5831_);
                        lean_dec(v_a_5821_);
                        v___x_5834_ = lean_box(0);
                        v_isShared_5835_ = v_isSharedCheck_5858_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5820_);
                    return v_b_5822_;
                }
            }
            1 => {
                v___x_5827_ = lean_string_utf8_extract(
                    v_val_5818_,
                    v_startInclusive_5825_,
                    v_endExclusive_5826_,
                );
                lean_dec(v_endExclusive_5826_);
                lean_dec(v_startInclusive_5825_);
                v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
                v___x_5829_ = lean_array_push(v_b_5822_, v___x_5828_);
                v_a_5821_ = v_it_5824_;
                v_b_5822_ = v___x_5829_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_5836_ = lean_ctor_get(v___x_5819_, 1);
                v_endExclusive_5837_ = lean_ctor_get(v___x_5819_, 2);
                v___x_5838_ = lean_nat_sub(v_endExclusive_5837_, v_startInclusive_5836_);
                v___x_5839_ = lean_nat_dec_eq(v_searcher_5832_, v___x_5838_);
                lean_dec(v___x_5838_);
                if v___x_5839_ == 0 {
                    v___x_5840_ = 10;
                    v___x_5841_ = lean_string_utf8_get_fast(v_val_5818_, v_searcher_5832_);
                    v___x_5842_ = lean_uint32_dec_eq(v___x_5841_, v___x_5840_);
                    if v___x_5842_ == 0 {
                        v___x_5843_ = lean_string_utf8_next_fast(v_val_5818_, v_searcher_5832_);
                        lean_dec(v_searcher_5832_);
                        if v_isShared_5835_ == 0 {
                            lean_ctor_set(v___x_5834_, 1, v___x_5843_);
                            v___x_5845_ = v___x_5834_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_currPos_5831_);
                            lean_ctor_set(v_reuseFailAlloc_5847_, 1, v___x_5843_);
                            v___x_5845_ = v_reuseFailAlloc_5847_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5848_ = lean_string_utf8_next_fast(v_val_5818_, v_searcher_5832_);
                        v___x_5849_ = lean_nat_sub(v___x_5848_, v_searcher_5832_);
                        v___x_5850_ = lean_nat_add(v_searcher_5832_, v___x_5849_);
                        lean_dec(v___x_5849_);
                        v_slice_5851_ = l_String_Slice_subslice_x21(
                            v___x_5819_,
                            v_currPos_5831_,
                            v_searcher_5832_,
                        );
                        lean_inc(v___x_5850_);
                        if v_isShared_5835_ == 0 {
                            lean_ctor_set(v___x_5834_, 1, v___x_5850_);
                            lean_ctor_set(v___x_5834_, 0, v___x_5850_);
                            v_nextIt_5853_ = v___x_5834_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5856_, 0, v___x_5850_);
                            lean_ctor_set(v_reuseFailAlloc_5856_, 1, v___x_5850_);
                            v_nextIt_5853_ = v_reuseFailAlloc_5856_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5834_);
                    lean_dec(v_searcher_5832_);
                    v___x_5857_ = lean_box(1);
                    lean_inc(v___x_5820_);
                    v_it_5824_ = v___x_5857_;
                    v_startInclusive_5825_ = v_currPos_5831_;
                    v_endExclusive_5826_ = v___x_5820_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_5821_ = v___x_5845_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_5854_ = lean_ctor_get(v_slice_5851_, 0);
                lean_inc(v_startInclusive_5854_);
                v_endExclusive_5855_ = lean_ctor_get(v_slice_5851_, 1);
                lean_inc(v_endExclusive_5855_);
                lean_dec_ref(v_slice_5851_);
                v_it_5824_ = v_nextIt_5853_;
                v_startInclusive_5825_ = v_startInclusive_5854_;
                v_endExclusive_5826_ = v_endExclusive_5855_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(
    mut v_val_5859_: *mut LeanObject,
    mut v___x_5860_: *mut LeanObject,
    mut v___x_5861_: *mut LeanObject,
    mut v_a_5862_: *mut LeanObject,
    mut v_b_5863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5864_: *mut LeanObject = core::ptr::null_mut();
    v_res_5864_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_5859_, v___x_5860_, v___x_5861_, v_a_5862_, v_b_5863_);
    lean_dec_ref(v___x_5860_);
    lean_dec_ref(v_val_5859_);
    return v_res_5864_;
}
pub unsafe fn _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2()
-> *mut LeanObject {
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    v___x_5868_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1;
    v___x_5869_ = l_Lean_stringToMessageData(v___x_5868_);
    return v___x_5869_;
}
pub unsafe fn _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4()
-> *mut LeanObject {
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    v___x_5871_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3;
    v___x_5872_ = l_Lean_stringToMessageData(v___x_5871_);
    return v___x_5872_;
}
pub unsafe fn _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6()
-> *mut LeanObject {
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    v___x_5874_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5;
    v___x_5875_ = l_Lean_stringToMessageData(v___x_5874_);
    return v___x_5875_;
}
pub unsafe fn _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9()
-> *mut LeanObject {
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    v___x_5879_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8;
    v___x_5880_ = l_Lean_MessageData_ofFormat(v___x_5879_);
    return v___x_5880_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(
    mut v_a_5881_: *mut LeanObject,
    mut v_a_5882_: *mut LeanObject,
    mut v_x_5883_: *mut LeanObject,
    mut v_x_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
    mut v___y_5886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5894_: u8 = 0;
    let mut v___y_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5912_: u8 = 0;
    let mut v_fst_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v___y_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: u8 = 0;
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: u8 = 0;
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: u8 = 0;
    let mut v___x_5984_: u8 = 0;
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5986_: u8 = 0;
    let mut v_isSharedCheck_5987_: u8 = 0;
    let mut v_isSharedCheck_5988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5883_) == 0 {
                    v___x_5888_ = l_List_reverse___redArg(v_x_5884_);
                    v___x_5889_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5889_, 0, v___x_5888_);
                    return v___x_5889_;
                } else {
                    v_head_5890_ = lean_ctor_get(v_x_5883_, 0);
                    v_tail_5891_ = lean_ctor_get(v_x_5883_, 1);
                    v_isSharedCheck_5988_ = (!lean_is_exclusive(v_x_5883_)) as u8;
                    if v_isSharedCheck_5988_ == 0 {
                        v___x_5893_ = v_x_5883_;
                        v_isShared_5894_ = v_isSharedCheck_5988_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5891_);
                        lean_inc(v_head_5890_);
                        lean_dec(v_x_5883_);
                        v___x_5893_ = lean_box(0);
                        v_isShared_5894_ = v_isSharedCheck_5988_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5908_ = lean_ctor_get(v_head_5890_, 1);
                v_fst_5909_ = lean_ctor_get(v_head_5890_, 0);
                v_isSharedCheck_5987_ = (!lean_is_exclusive(v_head_5890_)) as u8;
                if v_isSharedCheck_5987_ == 0 {
                    v___x_5911_ = v_head_5890_;
                    v_isShared_5912_ = v_isSharedCheck_5987_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_5908_);
                    lean_inc(v_fst_5909_);
                    lean_dec(v_head_5890_);
                    v___x_5911_ = lean_box(0);
                    v_isShared_5912_ = v_isSharedCheck_5987_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_5900_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5900_, 0, v___y_5898_);
                lean_ctor_set(v___x_5900_, 1, v___y_5899_);
                v___x_5901_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5901_, 0, v___x_5900_);
                lean_ctor_set(v___x_5901_, 1, v___y_5896_);
                v___x_5902_ = l_Lean_MessageData_nestD(v___x_5901_);
                lean_inc_ref(v___y_5897_);
                v___x_5903_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5903_, 0, v___y_5897_);
                lean_ctor_set(v___x_5903_, 1, v___x_5902_);
                if v_isShared_5894_ == 0 {
                    lean_ctor_set(v___x_5893_, 1, v_x_5884_);
                    lean_ctor_set(v___x_5893_, 0, v___x_5903_);
                    v___x_5905_ = v___x_5893_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5907_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5907_, 0, v___x_5903_);
                    lean_ctor_set(v_reuseFailAlloc_5907_, 1, v_x_5884_);
                    v___x_5905_ = v_reuseFailAlloc_5907_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_5883_ = v_tail_5891_;
                v_x_5884_ = v___x_5905_;
                state = 0;
                continue;
            }
            4 => {
                v_fst_5913_ = lean_ctor_get(v_snd_5908_, 0);
                v_snd_5914_ = lean_ctor_get(v_snd_5908_, 1);
                v_isSharedCheck_5986_ = (!lean_is_exclusive(v_snd_5908_)) as u8;
                if v_isSharedCheck_5986_ == 0 {
                    v___x_5916_ = v_snd_5908_;
                    v_isShared_5917_ = v_isSharedCheck_5986_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_5914_);
                    lean_inc(v_fst_5913_);
                    lean_dec(v_snd_5908_);
                    v___x_5916_ = lean_box(0);
                    v_isShared_5917_ = v_isSharedCheck_5986_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5966_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_5882_, v_fst_5909_);
                if lean_obj_tag(v___x_5966_) == 0 {
                    v___x_5967_ = l_Lean_MessageData_nil;
                    v_a_5941_ = v___x_5967_;
                    state = 9;
                    continue;
                } else {
                    v_val_5968_ = lean_ctor_get(v___x_5966_, 0);
                    lean_inc(v_val_5968_);
                    lean_dec_ref_known(v___x_5966_, 1);
                    if lean_obj_tag(v_val_5968_) == 0 {
                        v_size_5969_ = lean_ctor_get(v_val_5968_, 0);
                        v___x_5970_ = lean_mk_empty_array_with_capacity(v_size_5969_);
                        v___x_5971_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_5970_, v_val_5968_);
                        v___x_5972_ = lean_array_get_size(v___x_5971_);
                        v___x_5977_ = lean_unsigned_to_nat(0);
                        v___x_5978_ = lean_nat_dec_eq(v___x_5972_, v___x_5977_);
                        if v___x_5978_ == 0 {
                            v___x_5979_ = lean_unsigned_to_nat(1);
                            v___x_5980_ = lean_nat_sub(v___x_5972_, v___x_5979_);
                            v___x_5984_ = lean_nat_dec_le(v___x_5977_, v___x_5980_);
                            if v___x_5984_ == 0 {
                                lean_inc(v___x_5980_);
                                v___y_5982_ = v___x_5980_;
                                state = 12;
                                continue;
                            } else {
                                v___y_5982_ = v___x_5977_;
                                state = 12;
                                continue;
                            }
                        } else {
                            v___y_5957_ = v___x_5971_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_5985_ = l_Lean_MessageData_nil;
                        v_a_5941_ = v___x_5985_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5917_ == 0 {
                    lean_ctor_set_tag(v___x_5916_, 7);
                    lean_ctor_set(v___x_5916_, 1, v___y_5922_);
                    lean_ctor_set(v___x_5916_, 0, v___y_5920_);
                    v___x_5924_ = v___x_5916_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5939_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5939_, 0, v___y_5920_);
                    lean_ctor_set(v_reuseFailAlloc_5939_, 1, v___y_5922_);
                    v___x_5924_ = v_reuseFailAlloc_5939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if lean_obj_tag(v_snd_5914_) == 0 {
                    lean_del_object(v___x_5911_);
                    v___x_5925_ = l_Lean_MessageData_nil;
                    v___y_5896_ = v___y_5919_;
                    v___y_5897_ = v___y_5921_;
                    v___y_5898_ = v___x_5924_;
                    v___y_5899_ = v___x_5925_;
                    state = 2;
                    continue;
                } else {
                    v_val_5926_ = lean_ctor_get(v_snd_5914_, 0);
                    lean_inc_n(v_val_5926_, 2);
                    lean_dec_ref_known(v_snd_5914_, 1);
                    v___x_5927_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
                    v___x_5928_ = lean_unsigned_to_nat(0);
                    v___x_5929_ = lean_string_utf8_byte_size(v_val_5926_);
                    v___x_5930_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5930_, 0, v_val_5926_);
                    lean_ctor_set(v___x_5930_, 1, v___x_5928_);
                    lean_ctor_set(v___x_5930_, 2, v___x_5929_);
                    v___x_5931_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_5930_);
                    v___x_5932_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0;
                    v___x_5933_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_5926_, v___x_5930_, v___x_5929_, v___x_5931_, v___x_5932_);
                    lean_dec_ref_known(v___x_5930_, 3);
                    lean_dec(v_val_5926_);
                    v___x_5934_ = lean_array_to_list(v___x_5933_);
                    v___x_5935_ = l_Lean_MessageData_joinSep(v___x_5934_, v___x_5927_);
                    if v_isShared_5912_ == 0 {
                        lean_ctor_set_tag(v___x_5911_, 7);
                        lean_ctor_set(v___x_5911_, 1, v___x_5935_);
                        lean_ctor_set(v___x_5911_, 0, v___x_5927_);
                        v___x_5937_ = v___x_5911_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5938_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5938_, 0, v___x_5927_);
                        lean_ctor_set(v_reuseFailAlloc_5938_, 1, v___x_5935_);
                        v___x_5937_ = v_reuseFailAlloc_5938_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___y_5896_ = v___y_5919_;
                v___y_5897_ = v___y_5921_;
                v___y_5898_ = v___x_5924_;
                v___y_5899_ = v___x_5937_;
                state = 2;
                continue;
            }
            9 => {
                v___x_5942_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once), _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
                v___x_5943_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12,
                );
                lean_inc(v_fst_5909_);
                v___x_5944_ = l_Lean_MessageData_ofName(v_fst_5909_);
                v___x_5945_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5945_, 0, v___x_5943_);
                lean_ctor_set(v___x_5945_, 1, v___x_5944_);
                v___x_5946_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5946_, 0, v___x_5945_);
                lean_ctor_set(v___x_5946_, 1, v___x_5943_);
                v___x_5947_ = 1;
                v___x_5948_ = l_Lean_Name_toString(v_fst_5909_, v___x_5947_);
                v___x_5949_ = lean_string_dec_eq(v___x_5948_, v_fst_5913_);
                lean_dec_ref(v___x_5948_);
                if v___x_5949_ == 0 {
                    v___x_5950_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once), _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
                    v___x_5951_ = l_Lean_stringToMessageData(v_fst_5913_);
                    v___x_5952_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5952_, 0, v___x_5950_);
                    lean_ctor_set(v___x_5952_, 1, v___x_5951_);
                    v___x_5953_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once), _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
                    v___x_5954_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5954_, 0, v___x_5952_);
                    lean_ctor_set(v___x_5954_, 1, v___x_5953_);
                    v___y_5919_ = v_a_5941_;
                    v___y_5920_ = v___x_5946_;
                    v___y_5921_ = v___x_5942_;
                    v___y_5922_ = v___x_5954_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_fst_5913_);
                    v___x_5955_ = l_Lean_MessageData_nil;
                    v___y_5919_ = v_a_5941_;
                    v___y_5920_ = v___x_5946_;
                    v___y_5921_ = v___x_5942_;
                    v___y_5922_ = v___x_5955_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_5958_ = lean_array_to_list(v___y_5957_);
                v___x_5959_ = lean_box(0);
                v___x_5960_ =
                    l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(
                        v_a_5881_,
                        v___x_5958_,
                        v___x_5959_,
                        v___y_5885_,
                        v___y_5886_,
                    );
                if lean_obj_tag(v___x_5960_) == 0 {
                    v_a_5961_ = lean_ctor_get(v___x_5960_, 0);
                    lean_inc(v_a_5961_);
                    lean_dec_ref_known(v___x_5960_, 1);
                    v___x_5962_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
                    v___x_5963_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once), _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
                    v___x_5964_ = l_Lean_MessageData_joinSep(v_a_5961_, v___x_5963_);
                    v___x_5965_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5965_, 0, v___x_5962_);
                    lean_ctor_set(v___x_5965_, 1, v___x_5964_);
                    v_a_5941_ = v___x_5965_;
                    state = 9;
                    continue;
                } else {
                    lean_del_object(v___x_5916_);
                    lean_dec(v_snd_5914_);
                    lean_dec(v_fst_5913_);
                    lean_del_object(v___x_5911_);
                    lean_dec(v_fst_5909_);
                    lean_del_object(v___x_5893_);
                    lean_dec(v_tail_5891_);
                    lean_dec(v_x_5884_);
                    return v___x_5960_;
                }
            }
            11 => {
                v___x_5976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_5972_, v___x_5971_, v___y_5974_, v___y_5975_);
                lean_dec(v___y_5975_);
                v___y_5957_ = v___x_5976_;
                state = 10;
                continue;
            }
            12 => {
                v___x_5983_ = lean_nat_dec_le(v___y_5982_, v___x_5980_);
                if v___x_5983_ == 0 {
                    lean_dec(v___x_5980_);
                    lean_inc(v___y_5982_);
                    v___y_5974_ = v___y_5982_;
                    v___y_5975_ = v___y_5982_;
                    state = 11;
                    continue;
                } else {
                    v___y_5974_ = v___y_5982_;
                    v___y_5975_ = v___x_5980_;
                    state = 11;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(
    mut v_a_5989_: *mut LeanObject,
    mut v_a_5990_: *mut LeanObject,
    mut v_x_5991_: *mut LeanObject,
    mut v_x_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5996_: *mut LeanObject = core::ptr::null_mut();
    v_res_5996_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(
        v_a_5989_,
        v_a_5990_,
        v_x_5991_,
        v_x_5992_,
        v___y_5993_,
        v___y_5994_,
    );
    lean_dec(v___y_5994_);
    lean_dec_ref(v___y_5993_);
    lean_dec(v_a_5990_);
    lean_dec(v_a_5989_);
    return v_res_5996_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(
    mut v___y_5998_: u8,
    mut v_suppressElabErrors_5999_: u8,
    mut v_x_6000_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_6000_) == 1 {
        let mut v_pre_6001_: *mut LeanObject = core::ptr::null_mut();
        v_pre_6001_ = lean_ctor_get(v_x_6000_, 0);
        if lean_obj_tag(v_pre_6001_) == 0 {
            let mut v_str_6002_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6004_: u8 = 0;
            v_str_6002_ = lean_ctor_get(v_x_6000_, 1);
            v___x_6003_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0;
            v___x_6004_ = lean_string_dec_eq(v_str_6002_, v___x_6003_);
            if v___x_6004_ == 0 {
                return v___y_5998_;
            } else {
                return v_suppressElabErrors_5999_;
            }
        } else {
            return v___y_5998_;
        }
    } else {
        return v___y_5998_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(
    mut v___y_6005_: *mut LeanObject,
    mut v_suppressElabErrors_6006_: *mut LeanObject,
    mut v_x_6007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_18028__boxed_6008_: u8 = 0;
    let mut v_suppressElabErrors_boxed_6009_: u8 = 0;
    let mut v_res_6010_: u8 = 0;
    let mut v_r_6011_: *mut LeanObject = core::ptr::null_mut();
    v___y_18028__boxed_6008_ = (lean_unbox(v___y_6005_) as u8);
    v_suppressElabErrors_boxed_6009_ = (lean_unbox(v_suppressElabErrors_6006_) as u8);
    v_res_6010_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v___y_18028__boxed_6008_, v_suppressElabErrors_boxed_6009_, v_x_6007_);
    lean_dec(v_x_6007_);
    v_r_6011_ = lean_box((v_res_6010_) as usize);
    return v_r_6011_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(
    mut v_ref_6012_: *mut LeanObject,
    mut v_msgData_6013_: *mut LeanObject,
    mut v_severity_6014_: u8,
    mut v_isSilent_6015_: u8,
    mut v___y_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6020_: u8 = 0;
    let mut v___y_6021_: u8 = 0;
    let mut v___y_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6034_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6051_: u8 = 0;
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6064_: u8 = 0;
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_a_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_a_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6081_: u8 = 0;
    let mut v___y_6083_: u8 = 0;
    let mut v___y_6084_: u8 = 0;
    let mut v___y_6085_: u8 = 0;
    let mut v___y_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6090_: u8 = 0;
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6096_: u8 = 0;
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: u8 = 0;
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v___y_6111_: u8 = 0;
    let mut v___y_6112_: u8 = 0;
    let mut v___y_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: u8 = 0;
    let mut v___y_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: u8 = 0;
    let mut v___y_6120_: u8 = 0;
    let mut v___y_6121_: u8 = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6135_: u8 = 0;
    let mut v___x_6136_: u8 = 0;
    let mut v___y_6138_: u8 = 0;
    let mut v___y_6139_: u8 = 0;
    let mut v___y_6140_: u8 = 0;
    let mut v___y_6142_: u8 = 0;
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: u8 = 0;
    let mut v___x_6149_: u8 = 0;
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: u8 = 0;
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: u8 = 0;
    let mut v___x_6155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6136_ = 2;
                v___x_6154_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6014_, v___x_6136_);
                if v___x_6154_ == 0 {
                    v___y_6142_ = v___x_6154_;
                    state = 18;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_6013_);
                    v___x_6155_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6013_);
                    v___y_6142_ = v___x_6155_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_6028_ = l_Lean_Elab_Command_getScope___redArg(v___y_6027_);
                if lean_obj_tag(v___x_6028_) == 0 {
                    v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
                    lean_inc(v_a_6029_);
                    lean_dec_ref_known(v___x_6028_, 1);
                    v___x_6030_ = l_Lean_Elab_Command_getScope___redArg(v___y_6027_);
                    if lean_obj_tag(v___x_6030_) == 0 {
                        v_a_6031_ = lean_ctor_get(v___x_6030_, 0);
                        v_isSharedCheck_6065_ = (!lean_is_exclusive(v___x_6030_)) as u8;
                        if v_isSharedCheck_6065_ == 0 {
                            v___x_6033_ = v___x_6030_;
                            v_isShared_6034_ = v_isSharedCheck_6065_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6031_);
                            lean_dec(v___x_6030_);
                            v___x_6033_ = lean_box(0);
                            v_isShared_6034_ = v_isSharedCheck_6065_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6029_);
                        lean_dec_ref(v___y_6025_);
                        lean_dec(v___y_6024_);
                        lean_dec_ref(v___y_6022_);
                        v_a_6066_ = lean_ctor_get(v___x_6030_, 0);
                        v_isSharedCheck_6073_ = (!lean_is_exclusive(v___x_6030_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6030_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6066_);
                            lean_dec(v___x_6030_);
                            v___x_6068_ = lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6025_);
                    lean_dec(v___y_6024_);
                    lean_dec_ref(v___y_6022_);
                    v_a_6074_ = lean_ctor_get(v___x_6028_, 0);
                    v_isSharedCheck_6081_ = (!lean_is_exclusive(v___x_6028_)) as u8;
                    if v_isSharedCheck_6081_ == 0 {
                        v___x_6076_ = v___x_6028_;
                        v_isShared_6077_ = v_isSharedCheck_6081_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6074_);
                        lean_dec(v___x_6028_);
                        v___x_6076_ = lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6081_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6035_ = lean_st_ref_take(v___y_6027_);
                v_currNamespace_6036_ = lean_ctor_get(v_a_6029_, 2);
                lean_inc(v_currNamespace_6036_);
                lean_dec(v_a_6029_);
                v_openDecls_6037_ = lean_ctor_get(v_a_6031_, 3);
                lean_inc(v_openDecls_6037_);
                lean_dec(v_a_6031_);
                v_env_6038_ = lean_ctor_get(v___x_6035_, 0);
                v_messages_6039_ = lean_ctor_get(v___x_6035_, 1);
                v_scopes_6040_ = lean_ctor_get(v___x_6035_, 2);
                v_usedQuotCtxts_6041_ = lean_ctor_get(v___x_6035_, 3);
                v_nextMacroScope_6042_ = lean_ctor_get(v___x_6035_, 4);
                v_maxRecDepth_6043_ = lean_ctor_get(v___x_6035_, 5);
                v_ngen_6044_ = lean_ctor_get(v___x_6035_, 6);
                v_auxDeclNGen_6045_ = lean_ctor_get(v___x_6035_, 7);
                v_infoState_6046_ = lean_ctor_get(v___x_6035_, 8);
                v_traceState_6047_ = lean_ctor_get(v___x_6035_, 9);
                v_snapshotTasks_6048_ = lean_ctor_get(v___x_6035_, 10);
                v_isSharedCheck_6064_ = (!lean_is_exclusive(v___x_6035_)) as u8;
                if v_isSharedCheck_6064_ == 0 {
                    v___x_6050_ = v___x_6035_;
                    v_isShared_6051_ = v_isSharedCheck_6064_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6048_);
                    lean_inc(v_traceState_6047_);
                    lean_inc(v_infoState_6046_);
                    lean_inc(v_auxDeclNGen_6045_);
                    lean_inc(v_ngen_6044_);
                    lean_inc(v_maxRecDepth_6043_);
                    lean_inc(v_nextMacroScope_6042_);
                    lean_inc(v_usedQuotCtxts_6041_);
                    lean_inc(v_scopes_6040_);
                    lean_inc(v_messages_6039_);
                    lean_inc(v_env_6038_);
                    lean_dec(v___x_6035_);
                    v___x_6050_ = lean_box(0);
                    v_isShared_6051_ = v_isSharedCheck_6064_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6052_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6052_, 0, v_currNamespace_6036_);
                lean_ctor_set(v___x_6052_, 1, v_openDecls_6037_);
                v___x_6053_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_6053_, 0, v___x_6052_);
                lean_ctor_set(v___x_6053_, 1, v___y_6025_);
                lean_inc_ref(v___y_6026_);
                lean_inc_ref(v___y_6023_);
                v___x_6054_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_6054_, 0, v___y_6023_);
                lean_ctor_set(v___x_6054_, 1, v___y_6022_);
                lean_ctor_set(v___x_6054_, 2, v___y_6024_);
                lean_ctor_set(v___x_6054_, 3, v___y_6026_);
                lean_ctor_set(v___x_6054_, 4, v___x_6053_);
                lean_ctor_set_uint8(
                    v___x_6054_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_6021_,
                );
                lean_ctor_set_uint8(
                    v___x_6054_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_6020_,
                );
                lean_ctor_set_uint8(
                    v___x_6054_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_6015_,
                );
                v___x_6055_ = l_Lean_MessageLog_add(v___x_6054_, v_messages_6039_);
                if v_isShared_6051_ == 0 {
                    lean_ctor_set(v___x_6050_, 1, v___x_6055_);
                    v___x_6057_ = v___x_6050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_env_6038_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 1, v___x_6055_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 2, v_scopes_6040_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 3, v_usedQuotCtxts_6041_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 4, v_nextMacroScope_6042_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 5, v_maxRecDepth_6043_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 6, v_ngen_6044_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 7, v_auxDeclNGen_6045_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 8, v_infoState_6046_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 9, v_traceState_6047_);
                    lean_ctor_set(v_reuseFailAlloc_6063_, 10, v_snapshotTasks_6048_);
                    v___x_6057_ = v_reuseFailAlloc_6063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6058_ = lean_st_ref_set(v___y_6027_, v___x_6057_);
                v___x_6059_ = lean_box(0);
                if v_isShared_6034_ == 0 {
                    lean_ctor_set(v___x_6033_, 0, v___x_6059_);
                    v___x_6061_ = v___x_6033_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6062_, 0, v___x_6059_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6061_;
            }
            6 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6071_;
            }
            8 => {
                if v_isShared_6077_ == 0 {
                    v___x_6079_ = v___x_6076_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
                    v___x_6079_ = v_reuseFailAlloc_6080_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6079_;
            }
            10 => {
                v_fileName_6088_ = lean_ctor_get(v___y_6016_, 0);
                v_fileMap_6089_ = lean_ctor_get(v___y_6016_, 1);
                v_suppressElabErrors_6090_ = lean_ctor_get_uint8(
                    v___y_6016_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_6091_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_6013_,
                    );
                v___x_6092_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_6091_, v___y_6017_);
                v_a_6093_ = lean_ctor_get(v___x_6092_, 0);
                v_isSharedCheck_6109_ = (!lean_is_exclusive(v___x_6092_)) as u8;
                if v_isSharedCheck_6109_ == 0 {
                    v___x_6095_ = v___x_6092_;
                    v_isShared_6096_ = v_isSharedCheck_6109_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_6093_);
                    lean_dec(v___x_6092_);
                    v___x_6095_ = lean_box(0);
                    v_isShared_6096_ = v_isSharedCheck_6109_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_6089_, 2);
                v___x_6097_ = l_Lean_FileMap_toPosition(v_fileMap_6089_, v___y_6086_);
                lean_dec(v___y_6086_);
                v___x_6098_ = l_Lean_FileMap_toPosition(v_fileMap_6089_, v___y_6087_);
                lean_dec(v___y_6087_);
                v___x_6099_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6099_, 0, v___x_6098_);
                v___x_6100_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0;
                if v_suppressElabErrors_6090_ == 0 {
                    lean_del_object(v___x_6095_);
                    v___y_6020_ = v___y_6084_;
                    v___y_6021_ = v___y_6085_;
                    v___y_6022_ = v___x_6097_;
                    v___y_6023_ = v_fileName_6088_;
                    v___y_6024_ = v___x_6099_;
                    v___y_6025_ = v_a_6093_;
                    v___y_6026_ = v___x_6100_;
                    v___y_6027_ = v___y_6017_;
                    state = 1;
                    continue;
                } else {
                    v___x_6101_ = lean_box((v___y_6083_) as usize);
                    v___x_6102_ = lean_box((v_suppressElabErrors_6090_) as usize);
                    v___f_6103_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_6103_, 0, v___x_6101_);
                    lean_closure_set(v___f_6103_, 1, v___x_6102_);
                    lean_inc(v_a_6093_);
                    v___x_6104_ = l_Lean_MessageData_hasTag(v___f_6103_, v_a_6093_);
                    if v___x_6104_ == 0 {
                        lean_dec_ref_known(v___x_6099_, 1);
                        lean_dec_ref(v___x_6097_);
                        lean_dec(v_a_6093_);
                        v___x_6105_ = lean_box(0);
                        if v_isShared_6096_ == 0 {
                            lean_ctor_set(v___x_6095_, 0, v___x_6105_);
                            v___x_6107_ = v___x_6095_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6108_, 0, v___x_6105_);
                            v___x_6107_ = v_reuseFailAlloc_6108_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6095_);
                        v___y_6020_ = v___y_6084_;
                        v___y_6021_ = v___y_6085_;
                        v___y_6022_ = v___x_6097_;
                        v___y_6023_ = v_fileName_6088_;
                        v___y_6024_ = v___x_6099_;
                        v___y_6025_ = v_a_6093_;
                        v___y_6026_ = v___x_6100_;
                        v___y_6027_ = v___y_6017_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_6107_;
            }
            13 => {
                v___x_6116_ = l_Lean_Syntax_getTailPos_x3f(v___y_6113_, v___y_6114_);
                lean_dec(v___y_6113_);
                if lean_obj_tag(v___x_6116_) == 0 {
                    lean_inc(v___y_6115_);
                    v___y_6083_ = v___y_6111_;
                    v___y_6084_ = v___y_6112_;
                    v___y_6085_ = v___y_6114_;
                    v___y_6086_ = v___y_6115_;
                    v___y_6087_ = v___y_6115_;
                    state = 10;
                    continue;
                } else {
                    v_val_6117_ = lean_ctor_get(v___x_6116_, 0);
                    lean_inc(v_val_6117_);
                    lean_dec_ref_known(v___x_6116_, 1);
                    v___y_6083_ = v___y_6111_;
                    v___y_6084_ = v___y_6112_;
                    v___y_6085_ = v___y_6114_;
                    v___y_6086_ = v___y_6115_;
                    v___y_6087_ = v_val_6117_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_6122_ = l_Lean_Elab_Command_getRef___redArg(v___y_6016_);
                if lean_obj_tag(v___x_6122_) == 0 {
                    v_a_6123_ = lean_ctor_get(v___x_6122_, 0);
                    lean_inc(v_a_6123_);
                    lean_dec_ref_known(v___x_6122_, 1);
                    v_ref_6124_ = l_Lean_replaceRef(v_ref_6012_, v_a_6123_);
                    lean_dec(v_a_6123_);
                    v___x_6125_ = l_Lean_Syntax_getPos_x3f(v_ref_6124_, v___y_6120_);
                    if lean_obj_tag(v___x_6125_) == 0 {
                        v___x_6126_ = lean_unsigned_to_nat(0);
                        v___y_6111_ = v___y_6119_;
                        v___y_6112_ = v___y_6121_;
                        v___y_6113_ = v_ref_6124_;
                        v___y_6114_ = v___y_6120_;
                        v___y_6115_ = v___x_6126_;
                        state = 13;
                        continue;
                    } else {
                        v_val_6127_ = lean_ctor_get(v___x_6125_, 0);
                        lean_inc(v_val_6127_);
                        lean_dec_ref_known(v___x_6125_, 1);
                        v___y_6111_ = v___y_6119_;
                        v___y_6112_ = v___y_6121_;
                        v___y_6113_ = v_ref_6124_;
                        v___y_6114_ = v___y_6120_;
                        v___y_6115_ = v_val_6127_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_6013_);
                    v_a_6128_ = lean_ctor_get(v___x_6122_, 0);
                    v_isSharedCheck_6135_ = (!lean_is_exclusive(v___x_6122_)) as u8;
                    if v_isSharedCheck_6135_ == 0 {
                        v___x_6130_ = v___x_6122_;
                        v_isShared_6131_ = v_isSharedCheck_6135_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_6128_);
                        lean_dec(v___x_6122_);
                        v___x_6130_ = lean_box(0);
                        v_isShared_6131_ = v_isSharedCheck_6135_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_6131_ == 0 {
                    v___x_6133_ = v___x_6130_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_a_6128_);
                    v___x_6133_ = v_reuseFailAlloc_6134_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6133_;
            }
            17 => {
                if v___y_6140_ == 0 {
                    v___y_6119_ = v___y_6138_;
                    v___y_6120_ = v___y_6139_;
                    v___y_6121_ = v_severity_6014_;
                    state = 14;
                    continue;
                } else {
                    v___y_6119_ = v___y_6138_;
                    v___y_6120_ = v___y_6139_;
                    v___y_6121_ = v___x_6136_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_6142_ == 0 {
                    v___x_6143_ = lean_st_ref_get(v___y_6017_);
                    v_scopes_6144_ = lean_ctor_get(v___x_6143_, 2);
                    lean_inc(v_scopes_6144_);
                    lean_dec(v___x_6143_);
                    v___x_6145_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_6146_ = l_List_head_x21___redArg(v___x_6145_, v_scopes_6144_);
                    lean_dec(v_scopes_6144_);
                    v_opts_6147_ = lean_ctor_get(v___x_6146_, 1);
                    lean_inc_ref(v_opts_6147_);
                    lean_dec(v___x_6146_);
                    v___x_6148_ = 1;
                    v___x_6149_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6014_, v___x_6148_);
                    if v___x_6149_ == 0 {
                        lean_dec_ref(v_opts_6147_);
                        v___y_6138_ = v___y_6142_;
                        v___y_6139_ = v___y_6142_;
                        v___y_6140_ = v___x_6149_;
                        state = 17;
                        continue;
                    } else {
                        v___x_6150_ = l_Lean_warningAsError;
                        v___x_6151_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_6147_, v___x_6150_);
                        lean_dec_ref(v_opts_6147_);
                        v___y_6138_ = v___y_6142_;
                        v___y_6139_ = v___y_6142_;
                        v___y_6140_ = v___x_6151_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_6013_);
                    v___x_6152_ = lean_box(0);
                    v___x_6153_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6153_, 0, v___x_6152_);
                    return v___x_6153_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(
    mut v_ref_6156_: *mut LeanObject,
    mut v_msgData_6157_: *mut LeanObject,
    mut v_severity_6158_: *mut LeanObject,
    mut v_isSilent_6159_: *mut LeanObject,
    mut v___y_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6163_: u8 = 0;
    let mut v_isSilent_boxed_6164_: u8 = 0;
    let mut v_res_6165_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6163_ = (lean_unbox(v_severity_6158_) as u8);
    v_isSilent_boxed_6164_ = (lean_unbox(v_isSilent_6159_) as u8);
    v_res_6165_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_6156_, v_msgData_6157_, v_severity_boxed_6163_, v_isSilent_boxed_6164_, v___y_6160_, v___y_6161_);
    lean_dec(v___y_6161_);
    lean_dec_ref(v___y_6160_);
    lean_dec(v_ref_6156_);
    return v_res_6165_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(
    mut v_msgData_6166_: *mut LeanObject,
    mut v_severity_6167_: u8,
    mut v_isSilent_6168_: u8,
    mut v___y_6169_: *mut LeanObject,
    mut v___y_6170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6178_: u8 = 0;
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6172_ = l_Lean_Elab_Command_getRef___redArg(v___y_6169_);
                if lean_obj_tag(v___x_6172_) == 0 {
                    v_a_6173_ = lean_ctor_get(v___x_6172_, 0);
                    lean_inc(v_a_6173_);
                    lean_dec_ref_known(v___x_6172_, 1);
                    v___x_6174_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_6173_, v_msgData_6166_, v_severity_6167_, v_isSilent_6168_, v___y_6169_, v___y_6170_);
                    lean_dec(v_a_6173_);
                    return v___x_6174_;
                } else {
                    lean_dec_ref(v_msgData_6166_);
                    v_a_6175_ = lean_ctor_get(v___x_6172_, 0);
                    v_isSharedCheck_6182_ = (!lean_is_exclusive(v___x_6172_)) as u8;
                    if v_isSharedCheck_6182_ == 0 {
                        v___x_6177_ = v___x_6172_;
                        v_isShared_6178_ = v_isSharedCheck_6182_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6175_);
                        lean_dec(v___x_6172_);
                        v___x_6177_ = lean_box(0);
                        v_isShared_6178_ = v_isSharedCheck_6182_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6178_ == 0 {
                    v___x_6180_ = v___x_6177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
                    v___x_6180_ = v_reuseFailAlloc_6181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(
    mut v_msgData_6183_: *mut LeanObject,
    mut v_severity_6184_: *mut LeanObject,
    mut v_isSilent_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
    mut v___y_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6189_: u8 = 0;
    let mut v_isSilent_boxed_6190_: u8 = 0;
    let mut v_res_6191_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6189_ = (lean_unbox(v_severity_6184_) as u8);
    v_isSilent_boxed_6190_ = (lean_unbox(v_isSilent_6185_) as u8);
    v_res_6191_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_6183_, v_severity_boxed_6189_, v_isSilent_boxed_6190_, v___y_6186_, v___y_6187_);
    lean_dec(v___y_6187_);
    lean_dec_ref(v___y_6186_);
    return v_res_6191_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(
    mut v_msgData_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6196_: u8 = 0;
    let mut v___x_6197_: u8 = 0;
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    v___x_6196_ = 0;
    v___x_6197_ = 0;
    v___x_6198_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_6192_, v___x_6196_, v___x_6197_, v___y_6193_, v___y_6194_);
    return v___x_6198_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(
    mut v_msgData_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6203_: *mut LeanObject = core::ptr::null_mut();
    v_res_6203_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(
        v_msgData_6199_,
        v___y_6200_,
        v___y_6201_,
    );
    lean_dec(v___y_6201_);
    lean_dec_ref(v___y_6200_);
    return v_res_6203_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(
    mut v_init_6204_: *mut LeanObject,
    mut v_x_6205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6205_) == 0 {
                    v_k_6207_ = lean_ctor_get(v_x_6205_, 1);
                    lean_inc(v_k_6207_);
                    v_v_6208_ = lean_ctor_get(v_x_6205_, 2);
                    lean_inc(v_v_6208_);
                    v_l_6209_ = lean_ctor_get(v_x_6205_, 3);
                    lean_inc(v_l_6209_);
                    v_r_6210_ = lean_ctor_get(v_x_6205_, 4);
                    lean_inc(v_r_6210_);
                    lean_dec_ref_known(v_x_6205_, 5);
                    v___x_6211_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_6204_, v_l_6209_);
                    v_a_6212_ = lean_ctor_get(v___x_6211_, 0);
                    lean_inc(v_a_6212_);
                    lean_dec_ref(v___x_6211_);
                    v_a_6213_ = lean_ctor_get(v_a_6212_, 0);
                    lean_inc(v_a_6213_);
                    lean_dec(v_a_6212_);
                    v___x_6214_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_6207_, v_v_6208_, v_a_6213_);
                    v_init_6204_ = v___x_6214_;
                    v_x_6205_ = v_r_6210_;
                    state = 0;
                    continue;
                } else {
                    v___x_6216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6216_, 0, v_init_6204_);
                    v___x_6217_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6217_, 0, v___x_6216_);
                    return v___x_6217_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(
    mut v_init_6218_: *mut LeanObject,
    mut v_x_6219_: *mut LeanObject,
    mut v___y_6220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6221_: *mut LeanObject = core::ptr::null_mut();
    v_res_6221_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_6218_, v_x_6219_);
    return v_res_6221_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(
    mut v___x_6222_: u8,
    mut v_x1_6223_: *mut LeanObject,
    mut v_x2_6224_: *mut LeanObject,
) -> u8 {
    let mut v_fst_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: u8 = 0;
    v_fst_6225_ = lean_ctor_get(v_x1_6223_, 0);
    lean_inc(v_fst_6225_);
    lean_dec_ref(v_x1_6223_);
    v_fst_6226_ = lean_ctor_get(v_x2_6224_, 0);
    lean_inc(v_fst_6226_);
    lean_dec_ref(v_x2_6224_);
    v___x_6227_ = l_Lean_Name_toString(v_fst_6225_, v___x_6222_);
    v___x_6228_ = l_Lean_Name_toString(v_fst_6226_, v___x_6222_);
    v___x_6229_ = lean_string_dec_lt(v___x_6227_, v___x_6228_);
    lean_dec_ref(v___x_6228_);
    lean_dec_ref(v___x_6227_);
    return v___x_6229_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(
    mut v___x_6230_: *mut LeanObject,
    mut v_x1_6231_: *mut LeanObject,
    mut v_x2_6232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_18371__boxed_6233_: u8 = 0;
    let mut v_res_6234_: u8 = 0;
    let mut v_r_6235_: *mut LeanObject = core::ptr::null_mut();
    v___x_18371__boxed_6233_ = (lean_unbox(v___x_6230_) as u8);
    v_res_6234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18371__boxed_6233_, v_x1_6231_, v_x2_6232_);
    v_r_6235_ = lean_box((v_res_6234_) as usize);
    return v_r_6235_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(
    mut v_hi_6236_: *mut LeanObject,
    mut v_pivot_6237_: *mut LeanObject,
    mut v_as_6238_: *mut LeanObject,
    mut v_i_6239_: *mut LeanObject,
    mut v_k_6240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6241_: u8 = 0;
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: u8 = 0;
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6241_ = lean_nat_dec_lt(v_k_6240_, v_hi_6236_);
                if v___x_6241_ == 0 {
                    lean_dec(v_k_6240_);
                    lean_dec_ref(v_pivot_6237_);
                    v___x_6242_ = lean_array_fswap(v_as_6238_, v_i_6239_, v_hi_6236_);
                    v___x_6243_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6243_, 0, v_i_6239_);
                    lean_ctor_set(v___x_6243_, 1, v___x_6242_);
                    return v___x_6243_;
                } else {
                    v___x_6244_ = lean_array_fget_borrowed(v_as_6238_, v_k_6240_);
                    v_fst_6245_ = lean_ctor_get(v___x_6244_, 0);
                    v_fst_6246_ = lean_ctor_get(v_pivot_6237_, 0);
                    lean_inc(v_fst_6245_);
                    v___x_6247_ = l_Lean_Name_toString(v_fst_6245_, v___x_6241_);
                    lean_inc(v_fst_6246_);
                    v___x_6248_ = l_Lean_Name_toString(v_fst_6246_, v___x_6241_);
                    v___x_6249_ = lean_string_dec_lt(v___x_6247_, v___x_6248_);
                    lean_dec_ref(v___x_6248_);
                    lean_dec_ref(v___x_6247_);
                    if v___x_6249_ == 0 {
                        v___x_6250_ = lean_unsigned_to_nat(1);
                        v___x_6251_ = lean_nat_add(v_k_6240_, v___x_6250_);
                        lean_dec(v_k_6240_);
                        v_k_6240_ = v___x_6251_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6253_ = lean_array_fswap(v_as_6238_, v_i_6239_, v_k_6240_);
                        v___x_6254_ = lean_unsigned_to_nat(1);
                        v___x_6255_ = lean_nat_add(v_i_6239_, v___x_6254_);
                        lean_dec(v_i_6239_);
                        v___x_6256_ = lean_nat_add(v_k_6240_, v___x_6254_);
                        lean_dec(v_k_6240_);
                        v_as_6238_ = v___x_6253_;
                        v_i_6239_ = v___x_6255_;
                        v_k_6240_ = v___x_6256_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(
    mut v_hi_6258_: *mut LeanObject,
    mut v_pivot_6259_: *mut LeanObject,
    mut v_as_6260_: *mut LeanObject,
    mut v_i_6261_: *mut LeanObject,
    mut v_k_6262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6263_: *mut LeanObject = core::ptr::null_mut();
    v_res_6263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_6258_, v_pivot_6259_, v_as_6260_, v_i_6261_, v_k_6262_);
    lean_dec(v_hi_6258_);
    return v_res_6263_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(
    mut v_n_6264_: *mut LeanObject,
    mut v_as_6265_: *mut LeanObject,
    mut v_lo_6266_: *mut LeanObject,
    mut v_hi_6267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: u8 = 0;
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: u8 = 0;
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: u8 = 0;
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: u8 = 0;
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: u8 = 0;
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6279_ = lean_nat_dec_lt(v_lo_6266_, v_hi_6267_);
                if v___x_6279_ == 0 {
                    lean_dec(v_lo_6266_);
                    return v_as_6265_;
                } else {
                    v___x_6280_ = lean_nat_add(v_lo_6266_, v_hi_6267_);
                    v___x_6281_ = lean_unsigned_to_nat(1);
                    v_mid_6282_ = lean_nat_shiftr(v___x_6280_, v___x_6281_);
                    lean_dec(v___x_6280_);
                    v___x_6295_ = lean_array_fget_borrowed(v_as_6265_, v_mid_6282_);
                    v___x_6296_ = lean_array_fget_borrowed(v_as_6265_, v_lo_6266_);
                    lean_inc(v___x_6296_);
                    lean_inc(v___x_6295_);
                    v___x_6297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_6279_, v___x_6295_, v___x_6296_);
                    if v___x_6297_ == 0 {
                        v___y_6290_ = v_as_6265_;
                        state = 3;
                        continue;
                    } else {
                        v___x_6298_ = lean_array_fswap(v_as_6265_, v_lo_6266_, v_mid_6282_);
                        v___y_6290_ = v___x_6298_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_6270_ = lean_array_fget(v___y_6269_, v_hi_6267_);
                lean_inc_n(v_lo_6266_, 2);
                v___x_6271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_6267_, v_pivot_6270_, v___y_6269_, v_lo_6266_, v_lo_6266_);
                v_fst_6272_ = lean_ctor_get(v___x_6271_, 0);
                lean_inc(v_fst_6272_);
                v_snd_6273_ = lean_ctor_get(v___x_6271_, 1);
                lean_inc(v_snd_6273_);
                lean_dec_ref(v___x_6271_);
                v___x_6274_ = lean_nat_dec_le(v_hi_6267_, v_fst_6272_);
                if v___x_6274_ == 0 {
                    v___x_6275_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_6264_, v_snd_6273_, v_lo_6266_, v_fst_6272_);
                    v___x_6276_ = lean_unsigned_to_nat(1);
                    v___x_6277_ = lean_nat_add(v_fst_6272_, v___x_6276_);
                    lean_dec(v_fst_6272_);
                    v_as_6265_ = v___x_6275_;
                    v_lo_6266_ = v___x_6277_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_6272_);
                    lean_dec(v_lo_6266_);
                    return v_snd_6273_;
                }
            }
            2 => {
                v___x_6285_ = lean_array_fget_borrowed(v___y_6284_, v_mid_6282_);
                v___x_6286_ = lean_array_fget_borrowed(v___y_6284_, v_hi_6267_);
                lean_inc(v___x_6286_);
                lean_inc(v___x_6285_);
                v___x_6287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_6279_, v___x_6285_, v___x_6286_);
                if v___x_6287_ == 0 {
                    lean_dec(v_mid_6282_);
                    v___y_6269_ = v___y_6284_;
                    state = 1;
                    continue;
                } else {
                    v___x_6288_ = lean_array_fswap(v___y_6284_, v_mid_6282_, v_hi_6267_);
                    lean_dec(v_mid_6282_);
                    v___y_6269_ = v___x_6288_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6291_ = lean_array_fget_borrowed(v___y_6290_, v_hi_6267_);
                v___x_6292_ = lean_array_fget_borrowed(v___y_6290_, v_lo_6266_);
                lean_inc(v___x_6292_);
                lean_inc(v___x_6291_);
                v___x_6293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_6279_, v___x_6291_, v___x_6292_);
                if v___x_6293_ == 0 {
                    v___y_6284_ = v___y_6290_;
                    state = 2;
                    continue;
                } else {
                    v___x_6294_ = lean_array_fswap(v___y_6290_, v_lo_6266_, v_hi_6267_);
                    v___y_6284_ = v___x_6294_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(
    mut v_n_6299_: *mut LeanObject,
    mut v_as_6300_: *mut LeanObject,
    mut v_lo_6301_: *mut LeanObject,
    mut v_hi_6302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6303_: *mut LeanObject = core::ptr::null_mut();
    v_res_6303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_6299_, v_as_6300_, v_lo_6301_, v_hi_6302_);
    lean_dec(v_hi_6302_);
    lean_dec(v_n_6299_);
    return v_res_6303_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(
    mut v_init_6304_: *mut LeanObject,
    mut v_x_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6305_) == 0 {
                    v_k_6306_ = lean_ctor_get(v_x_6305_, 1);
                    v_v_6307_ = lean_ctor_get(v_x_6305_, 2);
                    v_l_6308_ = lean_ctor_get(v_x_6305_, 3);
                    v_r_6309_ = lean_ctor_get(v_x_6305_, 4);
                    v___x_6310_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_6304_, v_l_6308_);
                    lean_inc(v_v_6307_);
                    lean_inc(v_k_6306_);
                    v___x_6311_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6311_, 0, v_k_6306_);
                    lean_ctor_set(v___x_6311_, 1, v_v_6307_);
                    v___x_6312_ = lean_array_push(v___x_6310_, v___x_6311_);
                    v_init_6304_ = v___x_6312_;
                    v_x_6305_ = v_r_6309_;
                    state = 0;
                    continue;
                } else {
                    return v_init_6304_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(
    mut v_init_6314_: *mut LeanObject,
    mut v_x_6315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6316_: *mut LeanObject = core::ptr::null_mut();
    v_res_6316_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_6314_, v_x_6315_);
    lean_dec(v_x_6315_);
    return v_res_6316_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(
    mut v_as_6317_: *mut LeanObject,
    mut v_sz_6318_: usize,
    mut v_i_6319_: usize,
    mut v_b_6320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6322_: u8 = 0;
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: usize = 0;
    let mut v___x_6329_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6322_ = lean_usize_dec_lt(v_i_6319_, v_sz_6318_);
                if v___x_6322_ == 0 {
                    v___x_6323_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6323_, 0, v_b_6320_);
                    return v___x_6323_;
                } else {
                    v_a_6324_ = lean_array_uget_borrowed(v_as_6317_, v_i_6319_);
                    v_fst_6325_ = lean_ctor_get(v_a_6324_, 0);
                    v_snd_6326_ = lean_ctor_get(v_a_6324_, 1);
                    lean_inc(v_snd_6326_);
                    lean_inc(v_fst_6325_);
                    v_found_6327_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_6325_, v_snd_6326_, v_b_6320_);
                    v___x_6328_ = 1usize;
                    v___x_6329_ = lean_usize_add(v_i_6319_, v___x_6328_);
                    v_i_6319_ = v___x_6329_;
                    v_b_6320_ = v_found_6327_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(
    mut v_as_6331_: *mut LeanObject,
    mut v_sz_6332_: *mut LeanObject,
    mut v_i_6333_: *mut LeanObject,
    mut v_b_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6336_: usize = 0;
    let mut v_i_boxed_6337_: usize = 0;
    let mut v_res_6338_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6336_ = lean_unbox_usize(v_sz_6332_);
    lean_dec(v_sz_6332_);
    v_i_boxed_6337_ = lean_unbox_usize(v_i_6333_);
    lean_dec(v_i_6333_);
    v_res_6338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_6331_, v_sz_boxed_6336_, v_i_boxed_6337_, v_b_6334_);
    lean_dec_ref(v_as_6331_);
    return v_res_6338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(
    mut v_as_6339_: *mut LeanObject,
    mut v_sz_6340_: usize,
    mut v_i_6341_: usize,
    mut v_b_6342_: *mut LeanObject,
    mut v___y_6343_: *mut LeanObject,
    mut v___y_6344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6349_: usize = 0;
    let mut v___x_6350_: usize = 0;
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: usize = 0;
    let mut v___x_6354_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6346_ = lean_usize_dec_lt(v_i_6341_, v_sz_6340_);
                if v___x_6346_ == 0 {
                    v___x_6347_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6347_, 0, v_b_6342_);
                    return v___x_6347_;
                } else {
                    v_a_6348_ = lean_array_uget_borrowed(v_as_6339_, v_i_6341_);
                    v_sz_6349_ = lean_array_size(v_a_6348_);
                    v___x_6350_ = 0usize;
                    v___x_6351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_6348_, v_sz_6349_, v___x_6350_, v_b_6342_);
                    if lean_obj_tag(v___x_6351_) == 0 {
                        v_a_6352_ = lean_ctor_get(v___x_6351_, 0);
                        lean_inc(v_a_6352_);
                        lean_dec_ref_known(v___x_6351_, 1);
                        v___x_6353_ = 1usize;
                        v___x_6354_ = lean_usize_add(v_i_6341_, v___x_6353_);
                        v_i_6341_ = v___x_6354_;
                        v_b_6342_ = v_a_6352_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6351_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(
    mut v_as_6356_: *mut LeanObject,
    mut v_sz_6357_: *mut LeanObject,
    mut v_i_6358_: *mut LeanObject,
    mut v_b_6359_: *mut LeanObject,
    mut v___y_6360_: *mut LeanObject,
    mut v___y_6361_: *mut LeanObject,
    mut v___y_6362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6363_: usize = 0;
    let mut v_i_boxed_6364_: usize = 0;
    let mut v_res_6365_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6363_ = lean_unbox_usize(v_sz_6357_);
    lean_dec(v_sz_6357_);
    v_i_boxed_6364_ = lean_unbox_usize(v_i_6358_);
    lean_dec(v_i_6358_);
    v_res_6365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_6356_, v_sz_boxed_6363_, v_i_boxed_6364_, v_b_6359_, v___y_6360_, v___y_6361_);
    lean_dec(v___y_6361_);
    lean_dec_ref(v___y_6360_);
    lean_dec_ref(v_as_6356_);
    return v_res_6365_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0()
-> *mut LeanObject {
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    v___x_6366_ = lean_box(1);
    v___x_6367_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_6366_);
    return v___x_6367_;
}
pub unsafe fn l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(
    mut v___y_6370_: *mut LeanObject,
    mut v___y_6371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: u8 = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6404_: usize = 0;
    let mut v___x_6405_: usize = 0;
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arr_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: u8 = 0;
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: u8 = 0;
    let mut v_a_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6419_: u8 = 0;
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6423_: u8 = 0;
    let mut v_a_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6389_ = lean_st_ref_get(v___y_6371_);
                v_env_6390_ = lean_ctor_get(v___x_6389_, 0);
                lean_inc_ref_n(v_env_6390_, 2);
                lean_dec(v___x_6389_);
                v___x_6391_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
                v_toEnvExtension_6392_ = lean_ctor_get(v___x_6391_, 0);
                v_asyncMode_6393_ = lean_ctor_get(v_toEnvExtension_6392_, 2);
                v___x_6394_ = lean_box(1);
                v___x_6395_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once), _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
                v___x_6396_ = lean_box(0);
                v___x_6397_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_6394_,
                    v___x_6391_,
                    v_env_6390_,
                    v_asyncMode_6393_,
                    v___x_6396_,
                );
                v___x_6398_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_6394_, v___x_6397_);
                v_a_6399_ = lean_ctor_get(v___x_6398_, 0);
                lean_inc(v_a_6399_);
                lean_dec_ref(v___x_6398_);
                v_a_6424_ = lean_ctor_get(v_a_6399_, 0);
                lean_inc(v_a_6424_);
                lean_dec(v_a_6399_);
                v_a_6401_ = v_a_6424_;
                state = 4;
                continue;
            }
            1 => {
                v___x_6375_ = lean_array_to_list(v___y_6374_);
                v___x_6376_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6376_, 0, v___x_6375_);
                return v___x_6376_;
            }
            2 => {
                v___x_6382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_);
                lean_dec(v___y_6381_);
                lean_dec(v___y_6378_);
                v___y_6374_ = v___x_6382_;
                state = 1;
                continue;
            }
            3 => {
                v___x_6388_ = lean_nat_dec_le(v___y_6387_, v___y_6386_);
                if v___x_6388_ == 0 {
                    lean_dec(v___y_6386_);
                    lean_inc(v___y_6387_);
                    v___y_6378_ = v___y_6384_;
                    v___y_6379_ = v___y_6385_;
                    v___y_6380_ = v___y_6387_;
                    v___y_6381_ = v___y_6387_;
                    state = 2;
                    continue;
                } else {
                    v___y_6378_ = v___y_6384_;
                    v___y_6379_ = v___y_6385_;
                    v___y_6380_ = v___y_6387_;
                    v___y_6381_ = v___y_6386_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_6402_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_6395_,
                        v_toEnvExtension_6392_,
                        v_env_6390_,
                        v_asyncMode_6393_,
                        v___x_6396_,
                    );
                v_importedEntries_6403_ = lean_ctor_get(v___x_6402_, 0);
                lean_inc_ref(v_importedEntries_6403_);
                lean_dec(v___x_6402_);
                v_sz_6404_ = lean_array_size(v_importedEntries_6403_);
                v___x_6405_ = 0usize;
                v___x_6406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_6403_, v_sz_6404_, v___x_6405_, v_a_6401_, v___y_6370_, v___y_6371_);
                lean_dec_ref(v_importedEntries_6403_);
                if lean_obj_tag(v___x_6406_) == 0 {
                    v_a_6407_ = lean_ctor_get(v___x_6406_, 0);
                    lean_inc(v_a_6407_);
                    lean_dec_ref_known(v___x_6406_, 1);
                    v___x_6408_ = lean_unsigned_to_nat(0);
                    v___x_6409_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1;
                    v_arr_6410_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_6409_, v_a_6407_);
                    lean_dec(v_a_6407_);
                    v___x_6411_ = lean_array_get_size(v_arr_6410_);
                    v___x_6412_ = lean_nat_dec_eq(v___x_6411_, v___x_6408_);
                    if v___x_6412_ == 0 {
                        v___x_6413_ = lean_unsigned_to_nat(1);
                        v___x_6414_ = lean_nat_sub(v___x_6411_, v___x_6413_);
                        v___x_6415_ = lean_nat_dec_le(v___x_6408_, v___x_6414_);
                        if v___x_6415_ == 0 {
                            lean_inc(v___x_6414_);
                            v___y_6384_ = v___x_6411_;
                            v___y_6385_ = v_arr_6410_;
                            v___y_6386_ = v___x_6414_;
                            v___y_6387_ = v___x_6414_;
                            state = 3;
                            continue;
                        } else {
                            v___y_6384_ = v___x_6411_;
                            v___y_6385_ = v_arr_6410_;
                            v___y_6386_ = v___x_6414_;
                            v___y_6387_ = v___x_6408_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_6374_ = v_arr_6410_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6416_ = lean_ctor_get(v___x_6406_, 0);
                    v_isSharedCheck_6423_ = (!lean_is_exclusive(v___x_6406_)) as u8;
                    if v_isSharedCheck_6423_ == 0 {
                        v___x_6418_ = v___x_6406_;
                        v_isShared_6419_ = v_isSharedCheck_6423_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6416_);
                        lean_dec(v___x_6406_);
                        v___x_6418_ = lean_box(0);
                        v_isShared_6419_ = v_isSharedCheck_6423_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6419_ == 0 {
                    v___x_6421_ = v___x_6418_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6422_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6422_, 0, v_a_6416_);
                    v___x_6421_ = v_reuseFailAlloc_6422_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6428_: *mut LeanObject = core::ptr::null_mut();
    v_res_6428_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_6425_, v___y_6426_);
    lean_dec(v___y_6426_);
    lean_dec_ref(v___y_6425_);
    return v_res_6428_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(
    mut v_t_6429_: *mut LeanObject,
    mut v_k_6430_: *mut LeanObject,
    mut v_fallback_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6429_) == 0 {
                    v_k_6432_ = lean_ctor_get(v_t_6429_, 1);
                    v_v_6433_ = lean_ctor_get(v_t_6429_, 2);
                    v_l_6434_ = lean_ctor_get(v_t_6429_, 3);
                    v_r_6435_ = lean_ctor_get(v_t_6429_, 4);
                    v___x_6436_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6430_, v_k_6432_);
                    match v___x_6436_ {
                        0 => {
                            v_t_6429_ = v_l_6434_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_6433_);
                            return v_v_6433_;
                        }
                        _ => {
                            v_t_6429_ = v_r_6435_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_fallback_6431_);
                    return v_fallback_6431_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(
    mut v_t_6439_: *mut LeanObject,
    mut v_k_6440_: *mut LeanObject,
    mut v_fallback_6441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6442_: *mut LeanObject = core::ptr::null_mut();
    v_res_6442_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_6439_, v_k_6440_, v_fallback_6441_);
    lean_dec(v_fallback_6441_);
    lean_dec(v_k_6440_);
    lean_dec(v_t_6439_);
    return v_res_6442_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(
    mut v_as_6443_: *mut LeanObject,
    mut v_sz_6444_: usize,
    mut v_i_6445_: usize,
    mut v_b_6446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6448_: u8 = 0;
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: usize = 0;
    let mut v___x_6458_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6448_ = lean_usize_dec_lt(v_i_6445_, v_sz_6444_);
                if v___x_6448_ == 0 {
                    v___x_6449_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6449_, 0, v_b_6446_);
                    return v___x_6449_;
                } else {
                    v_a_6450_ = lean_array_uget_borrowed(v_as_6443_, v_i_6445_);
                    v_fst_6451_ = lean_ctor_get(v_a_6450_, 0);
                    v_snd_6452_ = lean_ctor_get(v_a_6450_, 1);
                    v___x_6453_ = l_Lean_NameSet_empty;
                    v___x_6454_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_6446_, v_snd_6452_, v___x_6453_);
                    lean_inc(v_fst_6451_);
                    v___x_6455_ = l_Lean_NameSet_insert(v___x_6454_, v_fst_6451_);
                    lean_inc(v_snd_6452_);
                    v___x_6456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_6452_, v___x_6455_, v_b_6446_);
                    v___x_6457_ = 1usize;
                    v___x_6458_ = lean_usize_add(v_i_6445_, v___x_6457_);
                    v_i_6445_ = v___x_6458_;
                    v_b_6446_ = v___x_6456_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(
    mut v_as_6460_: *mut LeanObject,
    mut v_sz_6461_: *mut LeanObject,
    mut v_i_6462_: *mut LeanObject,
    mut v_b_6463_: *mut LeanObject,
    mut v___y_6464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6465_: usize = 0;
    let mut v_i_boxed_6466_: usize = 0;
    let mut v_res_6467_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6465_ = lean_unbox_usize(v_sz_6461_);
    lean_dec(v_sz_6461_);
    v_i_boxed_6466_ = lean_unbox_usize(v_i_6462_);
    lean_dec(v_i_6462_);
    v_res_6467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_6460_, v_sz_boxed_6465_, v_i_boxed_6466_, v_b_6463_);
    lean_dec_ref(v_as_6460_);
    return v_res_6467_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(
    mut v_as_6468_: *mut LeanObject,
    mut v_sz_6469_: usize,
    mut v_i_6470_: usize,
    mut v_b_6471_: *mut LeanObject,
    mut v___y_6472_: *mut LeanObject,
    mut v___y_6473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6475_: u8 = 0;
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6478_: usize = 0;
    let mut v___x_6479_: usize = 0;
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: usize = 0;
    let mut v___x_6483_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6475_ = lean_usize_dec_lt(v_i_6470_, v_sz_6469_);
                if v___x_6475_ == 0 {
                    v___x_6476_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6476_, 0, v_b_6471_);
                    return v___x_6476_;
                } else {
                    v_a_6477_ = lean_array_uget_borrowed(v_as_6468_, v_i_6470_);
                    v_sz_6478_ = lean_array_size(v_a_6477_);
                    v___x_6479_ = 0usize;
                    v___x_6480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_6477_, v_sz_6478_, v___x_6479_, v_b_6471_);
                    if lean_obj_tag(v___x_6480_) == 0 {
                        v_a_6481_ = lean_ctor_get(v___x_6480_, 0);
                        lean_inc(v_a_6481_);
                        lean_dec_ref_known(v___x_6480_, 1);
                        v___x_6482_ = 1usize;
                        v___x_6483_ = lean_usize_add(v_i_6470_, v___x_6482_);
                        v_i_6470_ = v___x_6483_;
                        v_b_6471_ = v_a_6481_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6480_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(
    mut v_as_6485_: *mut LeanObject,
    mut v_sz_6486_: *mut LeanObject,
    mut v_i_6487_: *mut LeanObject,
    mut v_b_6488_: *mut LeanObject,
    mut v___y_6489_: *mut LeanObject,
    mut v___y_6490_: *mut LeanObject,
    mut v___y_6491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6492_: usize = 0;
    let mut v_i_boxed_6493_: usize = 0;
    let mut v_res_6494_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6492_ = lean_unbox_usize(v_sz_6486_);
    lean_dec(v_sz_6486_);
    v_i_boxed_6493_ = lean_unbox_usize(v_i_6487_);
    lean_dec(v_i_6487_);
    v_res_6494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_6485_, v_sz_boxed_6492_, v_i_boxed_6493_, v_b_6488_, v___y_6489_, v___y_6490_);
    lean_dec(v___y_6490_);
    lean_dec_ref(v___y_6489_);
    lean_dec_ref(v_as_6485_);
    return v_res_6494_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(
    mut v_as_6495_: *mut LeanObject,
    mut v_i_6496_: usize,
    mut v_stop_6497_: usize,
    mut v_b_6498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6499_: u8 = 0;
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: usize = 0;
    let mut v___x_6505_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6499_ = lean_usize_dec_eq(v_i_6496_, v_stop_6497_);
                if v___x_6499_ == 0 {
                    v___x_6500_ = lean_array_uget_borrowed(v_as_6495_, v_i_6496_);
                    v_fst_6501_ = lean_ctor_get(v___x_6500_, 0);
                    v_snd_6502_ = lean_ctor_get(v___x_6500_, 1);
                    lean_inc(v_snd_6502_);
                    lean_inc(v_fst_6501_);
                    v___x_6503_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_6501_, v_snd_6502_, v_b_6498_);
                    v___x_6504_ = 1usize;
                    v___x_6505_ = lean_usize_add(v_i_6496_, v___x_6504_);
                    v_i_6496_ = v___x_6505_;
                    v_b_6498_ = v___x_6503_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6498_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(
    mut v_as_6507_: *mut LeanObject,
    mut v_i_6508_: *mut LeanObject,
    mut v_stop_6509_: *mut LeanObject,
    mut v_b_6510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6511_: usize = 0;
    let mut v_stop_boxed_6512_: usize = 0;
    let mut v_res_6513_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6511_ = lean_unbox_usize(v_i_6508_);
    lean_dec(v_i_6508_);
    v_stop_boxed_6512_ = lean_unbox_usize(v_stop_6509_);
    lean_dec(v_stop_6509_);
    v_res_6513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_6507_, v_i_boxed_6511_, v_stop_boxed_6512_, v_b_6510_);
    lean_dec_ref(v_as_6507_);
    return v_res_6513_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(
    mut v_as_6514_: *mut LeanObject,
    mut v_i_6515_: usize,
    mut v_stop_6516_: usize,
    mut v_b_6517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: usize = 0;
    let mut v___x_6521_: usize = 0;
    let mut v___x_6523_: u8 = 0;
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: u8 = 0;
    let mut v___x_6528_: u8 = 0;
    let mut v___x_6529_: usize = 0;
    let mut v___x_6530_: usize = 0;
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: usize = 0;
    let mut v___x_6533_: usize = 0;
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6523_ = lean_usize_dec_eq(v_i_6515_, v_stop_6516_);
                if v___x_6523_ == 0 {
                    v___x_6524_ = lean_array_uget_borrowed(v_as_6514_, v_i_6515_);
                    v___x_6525_ = lean_unsigned_to_nat(0);
                    v___x_6526_ = lean_array_get_size(v___x_6524_);
                    v___x_6527_ = lean_nat_dec_lt(v___x_6525_, v___x_6526_);
                    if v___x_6527_ == 0 {
                        v___y_6519_ = v_b_6517_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6528_ = lean_nat_dec_le(v___x_6526_, v___x_6526_);
                        if v___x_6528_ == 0 {
                            if v___x_6527_ == 0 {
                                v___y_6519_ = v_b_6517_;
                                state = 1;
                                continue;
                            } else {
                                v___x_6529_ = 0usize;
                                v___x_6530_ = lean_usize_of_nat(v___x_6526_);
                                v___x_6531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_6524_, v___x_6529_, v___x_6530_, v_b_6517_);
                                v___y_6519_ = v___x_6531_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_6532_ = 0usize;
                            v___x_6533_ = lean_usize_of_nat(v___x_6526_);
                            v___x_6534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_6524_, v___x_6532_, v___x_6533_, v_b_6517_);
                            v___y_6519_ = v___x_6534_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_6517_;
                }
            }
            1 => {
                v___x_6520_ = 1usize;
                v___x_6521_ = lean_usize_add(v_i_6515_, v___x_6520_);
                v_i_6515_ = v___x_6521_;
                v_b_6517_ = v___y_6519_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(
    mut v_as_6535_: *mut LeanObject,
    mut v_i_6536_: *mut LeanObject,
    mut v_stop_6537_: *mut LeanObject,
    mut v_b_6538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6539_: usize = 0;
    let mut v_stop_boxed_6540_: usize = 0;
    let mut v_res_6541_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6539_ = lean_unbox_usize(v_i_6536_);
    lean_dec(v_i_6536_);
    v_stop_boxed_6540_ = lean_unbox_usize(v_stop_6537_);
    lean_dec(v_stop_6537_);
    v_res_6541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_6535_, v_i_boxed_6539_, v_stop_boxed_6540_, v_b_6538_);
    lean_dec_ref(v_as_6535_);
    return v_res_6541_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(
    mut v___y_6542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_categories_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6558_: u8 = 0;
    let mut v___y_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tables_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadingTable_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trailingTable_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstTokens_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstTokens_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: u8 = 0;
    let mut v___x_6586_: usize = 0;
    let mut v___x_6587_: usize = 0;
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: usize = 0;
    let mut v___x_6590_: usize = 0;
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6592_: u8 = 0;
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6544_ = lean_st_ref_get(v___y_6542_);
                v_env_6545_ = lean_ctor_get(v___x_6544_, 0);
                lean_inc_ref_n(v_env_6545_, 2);
                lean_dec(v___x_6544_);
                v___x_6546_ = l_Lean_Parser_parserExtension;
                v_ext_6547_ = lean_ctor_get(v___x_6546_, 1);
                v_toEnvExtension_6548_ = lean_ctor_get(v_ext_6547_, 0);
                v_asyncMode_6549_ = lean_ctor_get(v_toEnvExtension_6548_, 2);
                v___x_6550_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
                v___x_6551_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_6550_,
                    v___x_6546_,
                    v_env_6545_,
                    v_asyncMode_6549_,
                );
                v_categories_6552_ = lean_ctor_get(v___x_6551_, 2);
                lean_inc_ref(v_categories_6552_);
                lean_dec(v___x_6551_);
                v___x_6553_ =
                    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1;
                v___x_6554_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_6552_, v___x_6553_);
                lean_dec_ref(v_categories_6552_);
                if lean_obj_tag(v___x_6554_) == 1 {
                    v_val_6555_ = lean_ctor_get(v___x_6554_, 0);
                    v_isSharedCheck_6592_ = (!lean_is_exclusive(v___x_6554_)) as u8;
                    if v_isSharedCheck_6592_ == 0 {
                        v___x_6557_ = v___x_6554_;
                        v_isShared_6558_ = v_isSharedCheck_6592_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6555_);
                        lean_dec(v___x_6554_);
                        v___x_6557_ = lean_box(0);
                        v_isShared_6558_ = v_isSharedCheck_6592_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6554_);
                    lean_dec_ref(v_env_6545_);
                    v___x_6593_ = lean_box(1);
                    v___x_6594_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6594_, 0, v___x_6593_);
                    return v___x_6594_;
                }
            }
            1 => {
                v___x_6569_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
                v_toEnvExtension_6570_ = lean_ctor_get(v___x_6569_, 0);
                v_exportEntriesFn_6571_ = lean_ctor_get(v___x_6569_, 4);
                v_asyncMode_6572_ = lean_ctor_get(v_toEnvExtension_6570_, 2);
                v___x_6573_ = lean_box(1);
                v___x_6574_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2,
                );
                v___x_6575_ = lean_box(0);
                lean_inc_ref_n(v_env_6545_, 2);
                v___x_6576_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_6574_,
                        v_toEnvExtension_6570_,
                        v_env_6545_,
                        v_asyncMode_6572_,
                        v___x_6575_,
                    );
                v_importedEntries_6577_ = lean_ctor_get(v___x_6576_, 0);
                lean_inc_ref(v_importedEntries_6577_);
                lean_dec(v___x_6576_);
                v___x_6578_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_6573_,
                    v___x_6569_,
                    v_env_6545_,
                    v_asyncMode_6572_,
                    v___x_6575_,
                );
                lean_inc_ref(v_exportEntriesFn_6571_);
                v___x_6579_ = lean_apply_2(v_exportEntriesFn_6571_, v_env_6545_, v___x_6578_);
                v_exported_6580_ = lean_ctor_get(v___x_6579_, 0);
                lean_inc(v_exported_6580_);
                lean_dec_ref(v___x_6579_);
                v___x_6581_ = lean_array_push(v_importedEntries_6577_, v_exported_6580_);
                v___x_6582_ = lean_unsigned_to_nat(0);
                v___x_6583_ = lean_array_get_size(v___x_6581_);
                v___x_6584_ = lean_nat_dec_lt(v___x_6582_, v___x_6583_);
                if v___x_6584_ == 0 {
                    lean_dec_ref(v___x_6581_);
                    v___y_6560_ = v___x_6573_;
                    state = 2;
                    continue;
                } else {
                    v___x_6585_ = lean_nat_dec_le(v___x_6583_, v___x_6583_);
                    if v___x_6585_ == 0 {
                        if v___x_6584_ == 0 {
                            lean_dec_ref(v___x_6581_);
                            v___y_6560_ = v___x_6573_;
                            state = 2;
                            continue;
                        } else {
                            v___x_6586_ = 0usize;
                            v___x_6587_ = lean_usize_of_nat(v___x_6583_);
                            v___x_6588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_6581_, v___x_6586_, v___x_6587_, v___x_6573_);
                            lean_dec_ref(v___x_6581_);
                            v___y_6560_ = v___x_6588_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_6589_ = 0usize;
                        v___x_6590_ = lean_usize_of_nat(v___x_6583_);
                        v___x_6591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_6581_, v___x_6589_, v___x_6590_, v___x_6573_);
                        lean_dec_ref(v___x_6581_);
                        v___y_6560_ = v___x_6591_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_tables_6561_ = lean_ctor_get(v_val_6555_, 2);
                v_leadingTable_6562_ = lean_ctor_get(v_tables_6561_, 0);
                v_trailingTable_6563_ = lean_ctor_get(v_tables_6561_, 2);
                lean_inc(v_trailingTable_6563_);
                lean_inc(v_leadingTable_6562_);
                lean_inc(v_val_6555_);
                v_firstTokens_6564_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_6555_, v_leadingTable_6562_, v___y_6560_);
                v_firstTokens_6565_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_6555_, v_trailingTable_6563_, v_firstTokens_6564_);
                if v_isShared_6558_ == 0 {
                    lean_ctor_set_tag(v___x_6557_, 0);
                    lean_ctor_set(v___x_6557_, 0, v_firstTokens_6565_);
                    v___x_6567_ = v___x_6557_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6568_, 0, v_firstTokens_6565_);
                    v___x_6567_ = v_reuseFailAlloc_6568_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6597_: *mut LeanObject = core::ptr::null_mut();
    v_res_6597_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_6595_);
    lean_dec(v___y_6595_);
    return v_res_6597_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0() -> *mut LeanObject
{
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    v___x_6598_ = lean_box(1);
    v___x_6599_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_6598_);
    return v___x_6599_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2() -> *mut LeanObject
{
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    v___x_6601_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1;
    v___x_6602_ = l_Lean_stringToMessageData(v___x_6601_);
    return v___x_6602_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(
    mut v_a_6603_: *mut LeanObject,
    mut v_a_6604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6628_: usize = 0;
    let mut v___x_6629_: usize = 0;
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6655_: u8 = 0;
    let mut v_a_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6659_: u8 = 0;
    let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6663_: u8 = 0;
    let mut v_a_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6667_: u8 = 0;
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6671_: u8 = 0;
    let mut v_isSharedCheck_6672_: u8 = 0;
    let mut v_unused_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6606_ = lean_st_ref_get(v_a_6604_);
                v___x_6607_ = lean_st_ref_get(v_a_6604_);
                v___x_6608_ = lean_st_ref_get(v_a_6604_);
                v_env_6609_ = lean_ctor_get(v___x_6606_, 0);
                lean_inc_ref(v_env_6609_);
                lean_dec(v___x_6606_);
                v_env_6610_ = lean_ctor_get(v___x_6607_, 0);
                lean_inc_ref(v_env_6610_);
                lean_dec(v___x_6607_);
                v_env_6611_ = lean_ctor_get(v___x_6608_, 0);
                lean_inc_ref(v_env_6611_);
                lean_dec(v___x_6608_);
                v___x_6612_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
                v_toEnvExtension_6613_ = lean_ctor_get(v___x_6612_, 0);
                v_exportEntriesFn_6614_ = lean_ctor_get(v___x_6612_, 4);
                v_asyncMode_6615_ = lean_ctor_get(v_toEnvExtension_6613_, 2);
                v___x_6616_ = lean_box(1);
                v___x_6617_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0,
                );
                v___x_6618_ = lean_box(0);
                v___x_6619_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_6617_,
                        v_toEnvExtension_6613_,
                        v_env_6609_,
                        v_asyncMode_6615_,
                        v___x_6618_,
                    );
                v_importedEntries_6620_ = lean_ctor_get(v___x_6619_, 0);
                v_isSharedCheck_6672_ = (!lean_is_exclusive(v___x_6619_)) as u8;
                if v_isSharedCheck_6672_ == 0 {
                    v_unused_6673_ = lean_ctor_get(v___x_6619_, 1);
                    lean_dec(v_unused_6673_);
                    v___x_6622_ = v___x_6619_;
                    v_isShared_6623_ = v_isSharedCheck_6672_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_importedEntries_6620_);
                    lean_dec(v___x_6619_);
                    v___x_6622_ = lean_box(0);
                    v_isShared_6623_ = v_isSharedCheck_6672_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6624_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_6616_,
                    v___x_6612_,
                    v_env_6611_,
                    v_asyncMode_6615_,
                    v___x_6618_,
                );
                lean_inc_ref(v_exportEntriesFn_6614_);
                v___x_6625_ = lean_apply_2(v_exportEntriesFn_6614_, v_env_6610_, v___x_6624_);
                v_exported_6626_ = lean_ctor_get(v___x_6625_, 0);
                lean_inc(v_exported_6626_);
                lean_dec_ref(v___x_6625_);
                v___x_6627_ = lean_array_push(v_importedEntries_6620_, v_exported_6626_);
                v_sz_6628_ = lean_array_size(v___x_6627_);
                v___x_6629_ = 0usize;
                v___x_6630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_6627_, v_sz_6628_, v___x_6629_, v___x_6616_, v_a_6603_, v_a_6604_);
                lean_dec_ref(v___x_6627_);
                if lean_obj_tag(v___x_6630_) == 0 {
                    v_a_6631_ = lean_ctor_get(v___x_6630_, 0);
                    lean_inc(v_a_6631_);
                    lean_dec_ref_known(v___x_6630_, 1);
                    v___x_6632_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_6604_);
                    v_a_6633_ = lean_ctor_get(v___x_6632_, 0);
                    lean_inc(v_a_6633_);
                    lean_dec_ref(v___x_6632_);
                    v___x_6634_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_6603_, v_a_6604_);
                    if lean_obj_tag(v___x_6634_) == 0 {
                        v_a_6635_ = lean_ctor_get(v___x_6634_, 0);
                        lean_inc(v_a_6635_);
                        lean_dec_ref_known(v___x_6634_, 1);
                        v___x_6636_ = lean_box(0);
                        v___x_6637_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_6633_, v_a_6631_, v_a_6635_, v___x_6636_, v_a_6603_, v_a_6604_);
                        lean_dec(v_a_6631_);
                        lean_dec(v_a_6633_);
                        if lean_obj_tag(v___x_6637_) == 0 {
                            v_a_6638_ = lean_ctor_get(v___x_6637_, 0);
                            lean_inc(v_a_6638_);
                            lean_dec_ref_known(v___x_6637_, 1);
                            v___x_6639_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
                            v___x_6640_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
                            v___x_6641_ = l_Lean_MessageData_joinSep(v_a_6638_, v___x_6640_);
                            if v_isShared_6623_ == 0 {
                                lean_ctor_set_tag(v___x_6622_, 7);
                                lean_ctor_set(v___x_6622_, 1, v___x_6641_);
                                lean_ctor_set(v___x_6622_, 0, v___x_6640_);
                                v___x_6643_ = v___x_6622_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_6647_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6647_, 0, v___x_6640_);
                                lean_ctor_set(v_reuseFailAlloc_6647_, 1, v___x_6641_);
                                v___x_6643_ = v_reuseFailAlloc_6647_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_6622_);
                            v_a_6648_ = lean_ctor_get(v___x_6637_, 0);
                            v_isSharedCheck_6655_ = (!lean_is_exclusive(v___x_6637_)) as u8;
                            if v_isSharedCheck_6655_ == 0 {
                                v___x_6650_ = v___x_6637_;
                                v_isShared_6651_ = v_isSharedCheck_6655_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6648_);
                                lean_dec(v___x_6637_);
                                v___x_6650_ = lean_box(0);
                                v_isShared_6651_ = v_isSharedCheck_6655_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6633_);
                        lean_dec(v_a_6631_);
                        lean_del_object(v___x_6622_);
                        v_a_6656_ = lean_ctor_get(v___x_6634_, 0);
                        v_isSharedCheck_6663_ = (!lean_is_exclusive(v___x_6634_)) as u8;
                        if v_isSharedCheck_6663_ == 0 {
                            v___x_6658_ = v___x_6634_;
                            v_isShared_6659_ = v_isSharedCheck_6663_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_6656_);
                            lean_dec(v___x_6634_);
                            v___x_6658_ = lean_box(0);
                            v_isShared_6659_ = v_isSharedCheck_6663_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6622_);
                    v_a_6664_ = lean_ctor_get(v___x_6630_, 0);
                    v_isSharedCheck_6671_ = (!lean_is_exclusive(v___x_6630_)) as u8;
                    if v_isSharedCheck_6671_ == 0 {
                        v___x_6666_ = v___x_6630_;
                        v_isShared_6667_ = v_isSharedCheck_6671_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6664_);
                        lean_dec(v___x_6630_);
                        v___x_6666_ = lean_box(0);
                        v_isShared_6667_ = v_isSharedCheck_6671_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6644_ = l_Lean_MessageData_nestD(v___x_6643_);
                v___x_6645_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6645_, 0, v___x_6639_);
                lean_ctor_set(v___x_6645_, 1, v___x_6644_);
                v___x_6646_ =
                    l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(
                        v___x_6645_,
                        v_a_6603_,
                        v_a_6604_,
                    );
                return v___x_6646_;
            }
            3 => {
                if v_isShared_6651_ == 0 {
                    v___x_6653_ = v___x_6650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
                    v___x_6653_ = v_reuseFailAlloc_6654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6653_;
            }
            5 => {
                if v_isShared_6659_ == 0 {
                    v___x_6661_ = v___x_6658_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6662_, 0, v_a_6656_);
                    v___x_6661_ = v_reuseFailAlloc_6662_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6661_;
            }
            7 => {
                if v_isShared_6667_ == 0 {
                    v___x_6669_ = v___x_6666_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_a_6664_);
                    v___x_6669_ = v_reuseFailAlloc_6670_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(
    mut v_a_6674_: *mut LeanObject,
    mut v_a_6675_: *mut LeanObject,
    mut v_a_6676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6677_: *mut LeanObject = core::ptr::null_mut();
    v_res_6677_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_6674_, v_a_6675_);
    lean_dec(v_a_6675_);
    lean_dec_ref(v_a_6674_);
    return v_res_6677_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabPrintTacTags(
    mut v___stx_6678_: *mut LeanObject,
    mut v_a_6679_: *mut LeanObject,
    mut v_a_6680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    v___x_6682_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_6679_, v_a_6680_);
    return v___x_6682_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(
    mut v___stx_6683_: *mut LeanObject,
    mut v_a_6684_: *mut LeanObject,
    mut v_a_6685_: *mut LeanObject,
    mut v_a_6686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6687_: *mut LeanObject = core::ptr::null_mut();
    v_res_6687_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_6683_, v_a_6684_, v_a_6685_);
    lean_dec(v_a_6685_);
    lean_dec_ref(v_a_6684_);
    lean_dec(v___stx_6683_);
    return v_res_6687_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(
    mut v_00_u03b4_6688_: *mut LeanObject,
    mut v_t_6689_: *mut LeanObject,
    mut v_k_6690_: *mut LeanObject,
    mut v_fallback_6691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    v___x_6692_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_6689_, v_k_6690_, v_fallback_6691_);
    return v___x_6692_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(
    mut v_00_u03b4_6693_: *mut LeanObject,
    mut v_t_6694_: *mut LeanObject,
    mut v_k_6695_: *mut LeanObject,
    mut v_fallback_6696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6697_: *mut LeanObject = core::ptr::null_mut();
    v_res_6697_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_6693_, v_t_6694_, v_k_6695_, v_fallback_6696_);
    lean_dec(v_fallback_6696_);
    lean_dec(v_k_6695_);
    lean_dec(v_t_6694_);
    return v_res_6697_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(
    mut v_as_6698_: *mut LeanObject,
    mut v_sz_6699_: usize,
    mut v_i_6700_: usize,
    mut v_b_6701_: *mut LeanObject,
    mut v___y_6702_: *mut LeanObject,
    mut v___y_6703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    v___x_6705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_6698_, v_sz_6699_, v_i_6700_, v_b_6701_);
    return v___x_6705_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(
    mut v_as_6706_: *mut LeanObject,
    mut v_sz_6707_: *mut LeanObject,
    mut v_i_6708_: *mut LeanObject,
    mut v_b_6709_: *mut LeanObject,
    mut v___y_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
    mut v___y_6712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6713_: usize = 0;
    let mut v_i_boxed_6714_: usize = 0;
    let mut v_res_6715_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6713_ = lean_unbox_usize(v_sz_6707_);
    lean_dec(v_sz_6707_);
    v_i_boxed_6714_ = lean_unbox_usize(v_i_6708_);
    lean_dec(v_i_6708_);
    v_res_6715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_6706_, v_sz_boxed_6713_, v_i_boxed_6714_, v_b_6709_, v___y_6710_, v___y_6711_);
    lean_dec(v___y_6711_);
    lean_dec_ref(v___y_6710_);
    lean_dec_ref(v_as_6706_);
    return v_res_6715_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(
    mut v___y_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    v___x_6719_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_6717_);
    return v___x_6719_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6723_: *mut LeanObject = core::ptr::null_mut();
    v_res_6723_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_6720_, v___y_6721_);
    lean_dec(v___y_6721_);
    lean_dec_ref(v___y_6720_);
    return v_res_6723_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(
    mut v_val_6724_: *mut LeanObject,
    mut v___x_6725_: *mut LeanObject,
    mut v___x_6726_: *mut LeanObject,
    mut v_inst_6727_: *mut LeanObject,
    mut v_R_6728_: *mut LeanObject,
    mut v_a_6729_: *mut LeanObject,
    mut v_b_6730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    v___x_6731_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_6724_, v___x_6725_, v___x_6726_, v_a_6729_, v_b_6730_);
    return v___x_6731_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(
    mut v_val_6732_: *mut LeanObject,
    mut v___x_6733_: *mut LeanObject,
    mut v___x_6734_: *mut LeanObject,
    mut v_inst_6735_: *mut LeanObject,
    mut v_R_6736_: *mut LeanObject,
    mut v_a_6737_: *mut LeanObject,
    mut v_b_6738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6739_: *mut LeanObject = core::ptr::null_mut();
    v_res_6739_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_6732_, v___x_6733_, v___x_6734_, v_inst_6735_, v_R_6736_, v_a_6737_, v_b_6738_);
    lean_dec_ref(v___x_6733_);
    lean_dec_ref(v_val_6732_);
    return v_res_6739_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(
    mut v_init_6740_: *mut LeanObject,
    mut v_t_6741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    v___x_6742_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_6740_, v_t_6741_);
    return v___x_6742_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(
    mut v_n_6743_: *mut LeanObject,
    mut v_as_6744_: *mut LeanObject,
    mut v_lo_6745_: *mut LeanObject,
    mut v_hi_6746_: *mut LeanObject,
    mut v_w_6747_: *mut LeanObject,
    mut v_hlo_6748_: *mut LeanObject,
    mut v_hhi_6749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    v___x_6750_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_6743_, v_as_6744_, v_lo_6745_, v_hi_6746_);
    return v___x_6750_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(
    mut v_n_6751_: *mut LeanObject,
    mut v_as_6752_: *mut LeanObject,
    mut v_lo_6753_: *mut LeanObject,
    mut v_hi_6754_: *mut LeanObject,
    mut v_w_6755_: *mut LeanObject,
    mut v_hlo_6756_: *mut LeanObject,
    mut v_hhi_6757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6758_: *mut LeanObject = core::ptr::null_mut();
    v_res_6758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_6751_, v_as_6752_, v_lo_6753_, v_hi_6754_, v_w_6755_, v_hlo_6756_, v_hhi_6757_);
    lean_dec(v_hi_6754_);
    lean_dec(v_n_6751_);
    return v_res_6758_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(
    mut v_00_u03b2_6759_: *mut LeanObject,
    mut v_x_6760_: *mut LeanObject,
    mut v_x_6761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    v___x_6762_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_6760_, v_x_6761_);
    return v___x_6762_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(
    mut v_00_u03b2_6763_: *mut LeanObject,
    mut v_x_6764_: *mut LeanObject,
    mut v_x_6765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6766_: *mut LeanObject = core::ptr::null_mut();
    v_res_6766_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_6763_, v_x_6764_, v_x_6765_);
    lean_dec(v_x_6765_);
    lean_dec_ref(v_x_6764_);
    return v_res_6766_;
}
pub unsafe fn l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(
    mut v_tac_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
    mut v___y_6769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    v___x_6771_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_6767_, v___y_6769_);
    return v___x_6771_;
}
pub unsafe fn l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(
    mut v_tac_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
    mut v___y_6775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6776_: *mut LeanObject = core::ptr::null_mut();
    v_res_6776_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_6772_, v___y_6773_, v___y_6774_);
    lean_dec(v___y_6774_);
    lean_dec_ref(v___y_6773_);
    return v_res_6776_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(
    mut v_00_u03b4_6777_: *mut LeanObject,
    mut v_t_6778_: *mut LeanObject,
    mut v_k_6779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    v___x_6780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_6778_, v_k_6779_);
    return v___x_6780_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(
    mut v_00_u03b4_6781_: *mut LeanObject,
    mut v_t_6782_: *mut LeanObject,
    mut v_k_6783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6784_: *mut LeanObject = core::ptr::null_mut();
    v_res_6784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_6781_, v_t_6782_, v_k_6783_);
    lean_dec(v_k_6783_);
    lean_dec(v_t_6782_);
    return v_res_6784_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(
    mut v_00_u03b2_6785_: *mut LeanObject,
    mut v_x_6786_: *mut LeanObject,
    mut v_x_6787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    v___x_6788_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_6786_, v_x_6787_);
    return v___x_6788_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(
    mut v_00_u03b2_6789_: *mut LeanObject,
    mut v_x_6790_: *mut LeanObject,
    mut v_x_6791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6792_: *mut LeanObject = core::ptr::null_mut();
    v_res_6792_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_6789_, v_x_6790_, v_x_6791_);
    lean_dec(v_x_6791_);
    lean_dec_ref(v_x_6790_);
    return v_res_6792_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(
    mut v_n_6793_: *mut LeanObject,
    mut v_lo_6794_: *mut LeanObject,
    mut v_hi_6795_: *mut LeanObject,
    mut v_hhi_6796_: *mut LeanObject,
    mut v_pivot_6797_: *mut LeanObject,
    mut v_as_6798_: *mut LeanObject,
    mut v_i_6799_: *mut LeanObject,
    mut v_k_6800_: *mut LeanObject,
    mut v_ilo_6801_: *mut LeanObject,
    mut v_ik_6802_: *mut LeanObject,
    mut v_w_6803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    v___x_6804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_6795_, v_pivot_6797_, v_as_6798_, v_i_6799_, v_k_6800_);
    return v___x_6804_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(
    mut v_n_6805_: *mut LeanObject,
    mut v_lo_6806_: *mut LeanObject,
    mut v_hi_6807_: *mut LeanObject,
    mut v_hhi_6808_: *mut LeanObject,
    mut v_pivot_6809_: *mut LeanObject,
    mut v_as_6810_: *mut LeanObject,
    mut v_i_6811_: *mut LeanObject,
    mut v_k_6812_: *mut LeanObject,
    mut v_ilo_6813_: *mut LeanObject,
    mut v_ik_6814_: *mut LeanObject,
    mut v_w_6815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6816_: *mut LeanObject = core::ptr::null_mut();
    v_res_6816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_6805_, v_lo_6806_, v_hi_6807_, v_hhi_6808_, v_pivot_6809_, v_as_6810_, v_i_6811_, v_k_6812_, v_ilo_6813_, v_ik_6814_, v_w_6815_);
    lean_dec(v_hi_6807_);
    lean_dec(v_lo_6806_);
    lean_dec(v_n_6805_);
    return v_res_6816_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(
    mut v_as_6817_: *mut LeanObject,
    mut v_sz_6818_: usize,
    mut v_i_6819_: usize,
    mut v_b_6820_: *mut LeanObject,
    mut v___y_6821_: *mut LeanObject,
    mut v___y_6822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    v___x_6824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_6817_, v_sz_6818_, v_i_6819_, v_b_6820_);
    return v___x_6824_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(
    mut v_as_6825_: *mut LeanObject,
    mut v_sz_6826_: *mut LeanObject,
    mut v_i_6827_: *mut LeanObject,
    mut v_b_6828_: *mut LeanObject,
    mut v___y_6829_: *mut LeanObject,
    mut v___y_6830_: *mut LeanObject,
    mut v___y_6831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6832_: usize = 0;
    let mut v_i_boxed_6833_: usize = 0;
    let mut v_res_6834_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6832_ = lean_unbox_usize(v_sz_6826_);
    lean_dec(v_sz_6826_);
    v_i_boxed_6833_ = lean_unbox_usize(v_i_6827_);
    lean_dec(v_i_6827_);
    v_res_6834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_6825_, v_sz_boxed_6832_, v_i_boxed_6833_, v_b_6828_, v___y_6829_, v___y_6830_);
    lean_dec(v___y_6830_);
    lean_dec_ref(v___y_6829_);
    lean_dec_ref(v_as_6825_);
    return v_res_6834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(
    mut v_init_6835_: *mut LeanObject,
    mut v_t_6836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    v___x_6837_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_6835_, v_t_6836_);
    return v___x_6837_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(
    mut v_init_6838_: *mut LeanObject,
    mut v_t_6839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6840_: *mut LeanObject = core::ptr::null_mut();
    v_res_6840_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_6838_, v_t_6839_);
    lean_dec(v_t_6839_);
    return v_res_6840_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(
    mut v_n_6841_: *mut LeanObject,
    mut v_as_6842_: *mut LeanObject,
    mut v_lo_6843_: *mut LeanObject,
    mut v_hi_6844_: *mut LeanObject,
    mut v_w_6845_: *mut LeanObject,
    mut v_hlo_6846_: *mut LeanObject,
    mut v_hhi_6847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    v___x_6848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_6841_, v_as_6842_, v_lo_6843_, v_hi_6844_);
    return v___x_6848_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(
    mut v_n_6849_: *mut LeanObject,
    mut v_as_6850_: *mut LeanObject,
    mut v_lo_6851_: *mut LeanObject,
    mut v_hi_6852_: *mut LeanObject,
    mut v_w_6853_: *mut LeanObject,
    mut v_hlo_6854_: *mut LeanObject,
    mut v_hhi_6855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6856_: *mut LeanObject = core::ptr::null_mut();
    v_res_6856_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_6849_, v_as_6850_, v_lo_6851_, v_hi_6852_, v_w_6853_, v_hlo_6854_, v_hhi_6855_);
    lean_dec(v_hi_6852_);
    lean_dec(v_n_6849_);
    return v_res_6856_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(
    mut v_init_6857_: *mut LeanObject,
    mut v_x_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
    mut v___y_6860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    v___x_6862_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_6857_, v_x_6858_);
    return v___x_6862_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(
    mut v_init_6863_: *mut LeanObject,
    mut v_x_6864_: *mut LeanObject,
    mut v___y_6865_: *mut LeanObject,
    mut v___y_6866_: *mut LeanObject,
    mut v___y_6867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6868_: *mut LeanObject = core::ptr::null_mut();
    v_res_6868_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_6863_, v_x_6864_, v___y_6865_, v___y_6866_);
    lean_dec(v___y_6866_);
    lean_dec_ref(v___y_6865_);
    return v_res_6868_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(
    mut v_00_u03b2_6869_: *mut LeanObject,
    mut v_x_6870_: *mut LeanObject,
    mut v_x_6871_: usize,
    mut v_x_6872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    v___x_6873_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_6870_, v_x_6871_, v_x_6872_);
    return v___x_6873_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_6874_: *mut LeanObject,
    mut v_x_6875_: *mut LeanObject,
    mut v_x_6876_: *mut LeanObject,
    mut v_x_6877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_19099__boxed_6878_: usize = 0;
    let mut v_res_6879_: *mut LeanObject = core::ptr::null_mut();
    v_x_19099__boxed_6878_ = lean_unbox_usize(v_x_6876_);
    lean_dec(v_x_6876_);
    v_res_6879_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_6874_, v_x_6875_, v_x_19099__boxed_6878_, v_x_6877_);
    lean_dec(v_x_6877_);
    lean_dec_ref(v_x_6875_);
    return v_res_6879_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(
    mut v_as_6880_: *mut LeanObject,
    mut v_k_6881_: *mut LeanObject,
    mut v_x_6882_: *mut LeanObject,
    mut v_x_6883_: *mut LeanObject,
    mut v_x_6884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    v___x_6885_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_6880_, v_k_6881_, v_x_6882_, v_x_6883_);
    return v___x_6885_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(
    mut v_as_6886_: *mut LeanObject,
    mut v_k_6887_: *mut LeanObject,
    mut v_x_6888_: *mut LeanObject,
    mut v_x_6889_: *mut LeanObject,
    mut v_x_6890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6891_: *mut LeanObject = core::ptr::null_mut();
    v_res_6891_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_6886_, v_k_6887_, v_x_6888_, v_x_6889_, v_x_6890_);
    lean_dec_ref(v_k_6887_);
    lean_dec_ref(v_as_6886_);
    return v_res_6891_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(
    mut v_00_u03b2_6892_: *mut LeanObject,
    mut v_m_6893_: *mut LeanObject,
    mut v_a_6894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    v___x_6895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_6893_, v_a_6894_);
    return v___x_6895_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(
    mut v_00_u03b2_6896_: *mut LeanObject,
    mut v_m_6897_: *mut LeanObject,
    mut v_a_6898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6899_: *mut LeanObject = core::ptr::null_mut();
    v_res_6899_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_6896_, v_m_6897_, v_a_6898_);
    lean_dec(v_a_6898_);
    lean_dec_ref(v_m_6897_);
    return v_res_6899_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(
    mut v_n_6900_: *mut LeanObject,
    mut v_lo_6901_: *mut LeanObject,
    mut v_hi_6902_: *mut LeanObject,
    mut v_hhi_6903_: *mut LeanObject,
    mut v_pivot_6904_: *mut LeanObject,
    mut v_as_6905_: *mut LeanObject,
    mut v_i_6906_: *mut LeanObject,
    mut v_k_6907_: *mut LeanObject,
    mut v_ilo_6908_: *mut LeanObject,
    mut v_ik_6909_: *mut LeanObject,
    mut v_w_6910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    v___x_6911_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_6902_, v_pivot_6904_, v_as_6905_, v_i_6906_, v_k_6907_);
    return v___x_6911_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(
    mut v_n_6912_: *mut LeanObject,
    mut v_lo_6913_: *mut LeanObject,
    mut v_hi_6914_: *mut LeanObject,
    mut v_hhi_6915_: *mut LeanObject,
    mut v_pivot_6916_: *mut LeanObject,
    mut v_as_6917_: *mut LeanObject,
    mut v_i_6918_: *mut LeanObject,
    mut v_k_6919_: *mut LeanObject,
    mut v_ilo_6920_: *mut LeanObject,
    mut v_ik_6921_: *mut LeanObject,
    mut v_w_6922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6923_: *mut LeanObject = core::ptr::null_mut();
    v_res_6923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_6912_, v_lo_6913_, v_hi_6914_, v_hhi_6915_, v_pivot_6916_, v_as_6917_, v_i_6918_, v_k_6919_, v_ilo_6920_, v_ik_6921_, v_w_6922_);
    lean_dec(v_hi_6914_);
    lean_dec(v_lo_6913_);
    lean_dec(v_n_6912_);
    return v_res_6923_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(
    mut v_00_u03b2_6924_: *mut LeanObject,
    mut v_keys_6925_: *mut LeanObject,
    mut v_vals_6926_: *mut LeanObject,
    mut v_heq_6927_: *mut LeanObject,
    mut v_i_6928_: *mut LeanObject,
    mut v_k_6929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    v___x_6930_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_6925_, v_vals_6926_, v_i_6928_, v_k_6929_);
    return v___x_6930_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(
    mut v_00_u03b2_6931_: *mut LeanObject,
    mut v_keys_6932_: *mut LeanObject,
    mut v_vals_6933_: *mut LeanObject,
    mut v_heq_6934_: *mut LeanObject,
    mut v_i_6935_: *mut LeanObject,
    mut v_k_6936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6937_: *mut LeanObject = core::ptr::null_mut();
    v_res_6937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_6931_, v_keys_6932_, v_vals_6933_, v_heq_6934_, v_i_6935_, v_k_6936_);
    lean_dec(v_k_6936_);
    lean_dec_ref(v_vals_6933_);
    lean_dec_ref(v_keys_6932_);
    return v_res_6937_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(
    mut v_00_u03b2_6938_: *mut LeanObject,
    mut v_a_6939_: *mut LeanObject,
    mut v_x_6940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    v___x_6941_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_6939_, v_x_6940_);
    return v___x_6941_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(
    mut v_00_u03b2_6942_: *mut LeanObject,
    mut v_a_6943_: *mut LeanObject,
    mut v_x_6944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6945_: *mut LeanObject = core::ptr::null_mut();
    v_res_6945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_6942_, v_a_6943_, v_x_6944_);
    lean_dec(v_x_6944_);
    lean_dec(v_a_6943_);
    return v_res_6945_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1()
-> *mut LeanObject {
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    v___x_6960_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_6961_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1;
    v___x_6962_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3;
    v___x_6963_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_6964_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6960_,
        v___x_6961_,
        v___x_6962_,
        v___x_6963_,
    );
    return v___x_6964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(
    mut v_a_6965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6966_: *mut LeanObject = core::ptr::null_mut();
    v_res_6966_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
    return v_res_6966_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3()
-> *mut LeanObject {
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    v___x_6969_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3;
    v___x_6970_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0;
    v___x_6971_ = l_Lean_addBuiltinDocString(v___x_6969_, v___x_6970_);
    return v___x_6971_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(
    mut v_a_6972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6973_: *mut LeanObject = core::ptr::null_mut();
    v_res_6973_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
    return v_res_6973_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5()
-> *mut LeanObject {
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    v___x_7000_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3;
    v___x_7001_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6;
    v___x_7002_ = l_Lean_addBuiltinDeclarationRanges(v___x_7000_, v___x_7001_);
    return v___x_7002_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(
    mut v_a_7003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7004_: *mut LeanObject = core::ptr::null_mut();
    v_res_7004_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
    return v_res_7004_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(
    mut v_env_7005_: *mut LeanObject,
    mut v_a_7006_: *mut LeanObject,
    mut v_a_7007_: *mut LeanObject,
    mut v_includeUnnamed_7008_: u8,
    mut v_x_7009_: *mut LeanObject,
    mut v_____s_7010_: *mut LeanObject,
    mut v___y_7011_: *mut LeanObject,
    mut v___y_7012_: *mut LeanObject,
    mut v___y_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7019_: u8 = 0;
    let mut v_userName_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: u8 = 0;
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7028_: u8 = 0;
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7038_: u8 = 0;
    let mut v_a_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7042_: u8 = 0;
    let mut v_ref_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7053_: u8 = 0;
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7057_: u8 = 0;
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v_unused_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7069_: u8 = 0;
    let mut v_unused_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7016_ = lean_ctor_get(v_x_7009_, 0);
                v_isSharedCheck_7069_ = (!lean_is_exclusive(v_x_7009_)) as u8;
                if v_isSharedCheck_7069_ == 0 {
                    v_unused_7070_ = lean_ctor_get(v_x_7009_, 1);
                    lean_dec(v_unused_7070_);
                    v___x_7018_ = v_x_7009_;
                    v_isShared_7019_ = v_isSharedCheck_7069_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fst_7016_);
                    lean_dec(v_x_7009_);
                    v___x_7018_ = lean_box(0);
                    v_isShared_7019_ = v_isSharedCheck_7069_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_fst_7016_);
                lean_inc_ref(v_env_7005_);
                v___x_7054_ =
                    l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_7005_, v_fst_7016_);
                if lean_obj_tag(v___x_7054_) == 1 {
                    lean_del_object(v___x_7018_);
                    lean_dec(v_fst_7016_);
                    lean_dec_ref(v_env_7005_);
                    v_isSharedCheck_7062_ = (!lean_is_exclusive(v___x_7054_)) as u8;
                    if v_isSharedCheck_7062_ == 0 {
                        v_unused_7063_ = lean_ctor_get(v___x_7054_, 0);
                        lean_dec(v_unused_7063_);
                        v___x_7056_ = v___x_7054_;
                        v_isShared_7057_ = v_isSharedCheck_7062_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v___x_7054_);
                        v___x_7056_ = lean_box(0);
                        v_isShared_7057_ = v_isSharedCheck_7062_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7054_);
                    v___x_7064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_7007_, v_fst_7016_);
                    if lean_obj_tag(v___x_7064_) == 1 {
                        v_val_7065_ = lean_ctor_get(v___x_7064_, 0);
                        lean_inc(v_val_7065_);
                        lean_dec_ref_known(v___x_7064_, 1);
                        v_userName_7021_ = v_val_7065_;
                        v___y_7022_ = v___y_7013_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_7064_);
                        if v_includeUnnamed_7008_ == 0 {
                            lean_del_object(v___x_7018_);
                            lean_dec(v_fst_7016_);
                            lean_dec_ref(v_env_7005_);
                            v___x_7066_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_7066_, 0, v_____s_7010_);
                            v___x_7067_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_7067_, 0, v___x_7066_);
                            return v___x_7067_;
                        } else {
                            lean_inc(v_fst_7016_);
                            v___x_7068_ = l_Lean_Name_toString(v_fst_7016_, v_includeUnnamed_7008_);
                            v_userName_7021_ = v___x_7068_;
                            v___y_7022_ = v___y_7013_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_7023_ = 1;
                lean_inc(v_fst_7016_);
                lean_inc_ref(v_env_7005_);
                v___x_7024_ = l_Lean_findDocString_x3f(v_env_7005_, v_fst_7016_, v___x_7023_);
                if lean_obj_tag(v___x_7024_) == 0 {
                    lean_del_object(v___x_7018_);
                    v_a_7025_ = lean_ctor_get(v___x_7024_, 0);
                    v_isSharedCheck_7038_ = (!lean_is_exclusive(v___x_7024_)) as u8;
                    if v_isSharedCheck_7038_ == 0 {
                        v___x_7027_ = v___x_7024_;
                        v_isShared_7028_ = v_isSharedCheck_7038_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7025_);
                        lean_dec(v___x_7024_);
                        v___x_7027_ = lean_box(0);
                        v_isShared_7028_ = v_isSharedCheck_7038_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_userName_7021_);
                    lean_dec(v_fst_7016_);
                    lean_dec_ref(v_____s_7010_);
                    lean_dec_ref(v_env_7005_);
                    v_a_7039_ = lean_ctor_get(v___x_7024_, 0);
                    v_isSharedCheck_7053_ = (!lean_is_exclusive(v___x_7024_)) as u8;
                    if v_isSharedCheck_7053_ == 0 {
                        v___x_7041_ = v___x_7024_;
                        v_isShared_7042_ = v_isSharedCheck_7053_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7039_);
                        lean_dec(v___x_7024_);
                        v___x_7041_ = lean_box(0);
                        v_isShared_7042_ = v_isSharedCheck_7053_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7029_ = l_Lean_NameSet_empty;
                v___x_7030_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_7006_, v_fst_7016_, v___x_7029_);
                lean_inc(v_fst_7016_);
                v___x_7031_ =
                    l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_7005_, v_fst_7016_);
                v___x_7032_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_7032_, 0, v_fst_7016_);
                lean_ctor_set(v___x_7032_, 1, v_userName_7021_);
                lean_ctor_set(v___x_7032_, 2, v___x_7030_);
                lean_ctor_set(v___x_7032_, 3, v_a_7025_);
                lean_ctor_set(v___x_7032_, 4, v___x_7031_);
                v___x_7033_ = lean_array_push(v_____s_7010_, v___x_7032_);
                v___x_7034_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7034_, 0, v___x_7033_);
                if v_isShared_7028_ == 0 {
                    lean_ctor_set(v___x_7027_, 0, v___x_7034_);
                    v___x_7036_ = v___x_7027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7037_, 0, v___x_7034_);
                    v___x_7036_ = v_reuseFailAlloc_7037_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7036_;
            }
            5 => {
                v_ref_7043_ = lean_ctor_get(v___y_7022_, 5);
                v___x_7044_ = lean_io_error_to_string(v_a_7039_);
                v___x_7045_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_7045_, 0, v___x_7044_);
                v___x_7046_ = l_Lean_MessageData_ofFormat(v___x_7045_);
                lean_inc(v_ref_7043_);
                if v_isShared_7019_ == 0 {
                    lean_ctor_set(v___x_7018_, 1, v___x_7046_);
                    lean_ctor_set(v___x_7018_, 0, v_ref_7043_);
                    v___x_7048_ = v___x_7018_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7052_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7052_, 0, v_ref_7043_);
                    lean_ctor_set(v_reuseFailAlloc_7052_, 1, v___x_7046_);
                    v___x_7048_ = v_reuseFailAlloc_7052_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7042_ == 0 {
                    lean_ctor_set(v___x_7041_, 0, v___x_7048_);
                    v___x_7050_ = v___x_7041_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 0, v___x_7048_);
                    v___x_7050_ = v_reuseFailAlloc_7051_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7050_;
            }
            8 => {
                if v_isShared_7057_ == 0 {
                    lean_ctor_set(v___x_7056_, 0, v_____s_7010_);
                    v___x_7059_ = v___x_7056_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7061_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7061_, 0, v_____s_7010_);
                    v___x_7059_ = v_reuseFailAlloc_7061_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7060_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7060_, 0, v___x_7059_);
                return v___x_7060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(
    mut v_env_7071_: *mut LeanObject,
    mut v_a_7072_: *mut LeanObject,
    mut v_a_7073_: *mut LeanObject,
    mut v_includeUnnamed_7074_: *mut LeanObject,
    mut v_x_7075_: *mut LeanObject,
    mut v_____s_7076_: *mut LeanObject,
    mut v___y_7077_: *mut LeanObject,
    mut v___y_7078_: *mut LeanObject,
    mut v___y_7079_: *mut LeanObject,
    mut v___y_7080_: *mut LeanObject,
    mut v___y_7081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeUnnamed_boxed_7082_: u8 = 0;
    let mut v_res_7083_: *mut LeanObject = core::ptr::null_mut();
    v_includeUnnamed_boxed_7082_ = (lean_unbox(v_includeUnnamed_7074_) as u8);
    v_res_7083_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(
        v_env_7071_,
        v_a_7072_,
        v_a_7073_,
        v_includeUnnamed_boxed_7082_,
        v_x_7075_,
        v_____s_7076_,
        v___y_7077_,
        v___y_7078_,
        v___y_7079_,
        v___y_7080_,
    );
    lean_dec(v___y_7080_);
    lean_dec_ref(v___y_7079_);
    lean_dec(v___y_7078_);
    lean_dec_ref(v___y_7077_);
    lean_dec(v_a_7073_);
    lean_dec(v_a_7072_);
    return v_res_7083_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(
    mut v_as_7084_: *mut LeanObject,
    mut v_sz_7085_: usize,
    mut v_i_7086_: usize,
    mut v_b_7087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7089_: u8 = 0;
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: usize = 0;
    let mut v___x_7099_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7089_ = lean_usize_dec_lt(v_i_7086_, v_sz_7085_);
                if v___x_7089_ == 0 {
                    v___x_7090_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7090_, 0, v_b_7087_);
                    return v___x_7090_;
                } else {
                    v_a_7091_ = lean_array_uget_borrowed(v_as_7084_, v_i_7086_);
                    v_fst_7092_ = lean_ctor_get(v_a_7091_, 0);
                    v_snd_7093_ = lean_ctor_get(v_a_7091_, 1);
                    v___x_7094_ = l_Lean_NameSet_empty;
                    v___x_7095_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_7087_, v_fst_7092_, v___x_7094_);
                    lean_inc(v_snd_7093_);
                    v___x_7096_ = l_Lean_NameSet_insert(v___x_7095_, v_snd_7093_);
                    lean_inc(v_fst_7092_);
                    v___x_7097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_7092_, v___x_7096_, v_b_7087_);
                    v___x_7098_ = 1usize;
                    v___x_7099_ = lean_usize_add(v_i_7086_, v___x_7098_);
                    v_i_7086_ = v___x_7099_;
                    v_b_7087_ = v___x_7097_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(
    mut v_as_7101_: *mut LeanObject,
    mut v_sz_7102_: *mut LeanObject,
    mut v_i_7103_: *mut LeanObject,
    mut v_b_7104_: *mut LeanObject,
    mut v___y_7105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7106_: usize = 0;
    let mut v_i_boxed_7107_: usize = 0;
    let mut v_res_7108_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7106_ = lean_unbox_usize(v_sz_7102_);
    lean_dec(v_sz_7102_);
    v_i_boxed_7107_ = lean_unbox_usize(v_i_7103_);
    lean_dec(v_i_7103_);
    v_res_7108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_7101_, v_sz_boxed_7106_, v_i_boxed_7107_, v_b_7104_);
    lean_dec_ref(v_as_7101_);
    return v_res_7108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(
    mut v_as_7109_: *mut LeanObject,
    mut v_sz_7110_: usize,
    mut v_i_7111_: usize,
    mut v_b_7112_: *mut LeanObject,
    mut v___y_7113_: *mut LeanObject,
    mut v___y_7114_: *mut LeanObject,
    mut v___y_7115_: *mut LeanObject,
    mut v___y_7116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7118_: u8 = 0;
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7121_: usize = 0;
    let mut v___x_7122_: usize = 0;
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: usize = 0;
    let mut v___x_7126_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7118_ = lean_usize_dec_lt(v_i_7111_, v_sz_7110_);
                if v___x_7118_ == 0 {
                    v___x_7119_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7119_, 0, v_b_7112_);
                    return v___x_7119_;
                } else {
                    v_a_7120_ = lean_array_uget_borrowed(v_as_7109_, v_i_7111_);
                    v_sz_7121_ = lean_array_size(v_a_7120_);
                    v___x_7122_ = 0usize;
                    v___x_7123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_7120_, v_sz_7121_, v___x_7122_, v_b_7112_);
                    if lean_obj_tag(v___x_7123_) == 0 {
                        v_a_7124_ = lean_ctor_get(v___x_7123_, 0);
                        lean_inc(v_a_7124_);
                        lean_dec_ref_known(v___x_7123_, 1);
                        v___x_7125_ = 1usize;
                        v___x_7126_ = lean_usize_add(v_i_7111_, v___x_7125_);
                        v_i_7111_ = v___x_7126_;
                        v_b_7112_ = v_a_7124_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7123_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(
    mut v_as_7128_: *mut LeanObject,
    mut v_sz_7129_: *mut LeanObject,
    mut v_i_7130_: *mut LeanObject,
    mut v_b_7131_: *mut LeanObject,
    mut v___y_7132_: *mut LeanObject,
    mut v___y_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
    mut v___y_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7137_: usize = 0;
    let mut v_i_boxed_7138_: usize = 0;
    let mut v_res_7139_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7137_ = lean_unbox_usize(v_sz_7129_);
    lean_dec(v_sz_7129_);
    v_i_boxed_7138_ = lean_unbox_usize(v_i_7130_);
    lean_dec(v_i_7130_);
    v_res_7139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_7128_, v_sz_boxed_7137_, v_i_boxed_7138_, v_b_7131_, v___y_7132_, v___y_7133_, v___y_7134_, v___y_7135_);
    lean_dec(v___y_7135_);
    lean_dec_ref(v___y_7134_);
    lean_dec(v___y_7133_);
    lean_dec_ref(v___y_7132_);
    lean_dec_ref(v_as_7128_);
    return v_res_7139_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(
    mut v_f_7140_: *mut LeanObject,
    mut v_keys_7141_: *mut LeanObject,
    mut v_vals_7142_: *mut LeanObject,
    mut v_i_7143_: *mut LeanObject,
    mut v_acc_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
    mut v___y_7146_: *mut LeanObject,
    mut v___y_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: u8 = 0;
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7150_ = lean_array_get_size(v_keys_7141_);
                v___x_7151_ = lean_nat_dec_lt(v_i_7143_, v___x_7150_);
                if v___x_7151_ == 0 {
                    lean_dec(v_i_7143_);
                    lean_dec_ref(v_f_7140_);
                    v___x_7152_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7152_, 0, v_acc_7144_);
                    v___x_7153_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7153_, 0, v___x_7152_);
                    return v___x_7153_;
                } else {
                    v_k_7154_ = lean_array_fget_borrowed(v_keys_7141_, v_i_7143_);
                    v_v_7155_ = lean_array_fget_borrowed(v_vals_7142_, v_i_7143_);
                    lean_inc_ref(v_f_7140_);
                    lean_inc(v___y_7148_);
                    lean_inc_ref(v___y_7147_);
                    lean_inc(v___y_7146_);
                    lean_inc_ref(v___y_7145_);
                    lean_inc(v_v_7155_);
                    lean_inc(v_k_7154_);
                    v___x_7156_ = lean_apply_8(
                        v_f_7140_,
                        v_acc_7144_,
                        v_k_7154_,
                        v_v_7155_,
                        v___y_7145_,
                        v___y_7146_,
                        v___y_7147_,
                        v___y_7148_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_7156_) == 0 {
                        v_a_7157_ = lean_ctor_get(v___x_7156_, 0);
                        lean_inc(v_a_7157_);
                        if lean_obj_tag(v_a_7157_) == 0 {
                            lean_dec_ref_known(v_a_7157_, 1);
                            lean_dec(v_i_7143_);
                            lean_dec_ref(v_f_7140_);
                            return v___x_7156_;
                        } else {
                            lean_dec_ref_known(v___x_7156_, 1);
                            v_a_7158_ = lean_ctor_get(v_a_7157_, 0);
                            lean_inc(v_a_7158_);
                            lean_dec_ref_known(v_a_7157_, 1);
                            v___x_7159_ = lean_unsigned_to_nat(1);
                            v___x_7160_ = lean_nat_add(v_i_7143_, v___x_7159_);
                            lean_dec(v_i_7143_);
                            v_i_7143_ = v___x_7160_;
                            v_acc_7144_ = v_a_7158_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_7143_);
                        lean_dec_ref(v_f_7140_);
                        return v___x_7156_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_f_7162_: *mut LeanObject,
    mut v_keys_7163_: *mut LeanObject,
    mut v_vals_7164_: *mut LeanObject,
    mut v_i_7165_: *mut LeanObject,
    mut v_acc_7166_: *mut LeanObject,
    mut v___y_7167_: *mut LeanObject,
    mut v___y_7168_: *mut LeanObject,
    mut v___y_7169_: *mut LeanObject,
    mut v___y_7170_: *mut LeanObject,
    mut v___y_7171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7172_: *mut LeanObject = core::ptr::null_mut();
    v_res_7172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_7162_, v_keys_7163_, v_vals_7164_, v_i_7165_, v_acc_7166_, v___y_7167_, v___y_7168_, v___y_7169_, v___y_7170_);
    lean_dec(v___y_7170_);
    lean_dec_ref(v___y_7169_);
    lean_dec(v___y_7168_);
    lean_dec_ref(v___y_7167_);
    lean_dec_ref(v_vals_7164_);
    lean_dec_ref(v_keys_7163_);
    return v_res_7172_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(
    mut v_f_7173_: *mut LeanObject,
    mut v_x_7174_: *mut LeanObject,
    mut v_x_7175_: *mut LeanObject,
    mut v___y_7176_: *mut LeanObject,
    mut v___y_7177_: *mut LeanObject,
    mut v___y_7178_: *mut LeanObject,
    mut v___y_7179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7184_: u8 = 0;
    let mut v___x_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: u8 = 0;
    let mut v___x_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: u8 = 0;
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: usize = 0;
    let mut v___x_7198_: usize = 0;
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: usize = 0;
    let mut v___x_7201_: usize = 0;
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7203_: u8 = 0;
    let mut v_ks_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7174_) == 0 {
                    v_es_7181_ = lean_ctor_get(v_x_7174_, 0);
                    v_isSharedCheck_7203_ = (!lean_is_exclusive(v_x_7174_)) as u8;
                    if v_isSharedCheck_7203_ == 0 {
                        v___x_7183_ = v_x_7174_;
                        v_isShared_7184_ = v_isSharedCheck_7203_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_7181_);
                        lean_dec(v_x_7174_);
                        v___x_7183_ = lean_box(0);
                        v_isShared_7184_ = v_isSharedCheck_7203_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_7204_ = lean_ctor_get(v_x_7174_, 0);
                    lean_inc_ref(v_ks_7204_);
                    v_vs_7205_ = lean_ctor_get(v_x_7174_, 1);
                    lean_inc_ref(v_vs_7205_);
                    lean_dec_ref_known(v_x_7174_, 2);
                    v___x_7206_ = lean_unsigned_to_nat(0);
                    v___x_7207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_7173_, v_ks_7204_, v_vs_7205_, v___x_7206_, v_x_7175_, v___y_7176_, v___y_7177_, v___y_7178_, v___y_7179_);
                    lean_dec_ref(v_vs_7205_);
                    lean_dec_ref(v_ks_7204_);
                    return v___x_7207_;
                }
            }
            1 => {
                v___x_7185_ = lean_unsigned_to_nat(0);
                v___x_7186_ = lean_array_get_size(v_es_7181_);
                v___x_7187_ = lean_nat_dec_lt(v___x_7185_, v___x_7186_);
                if v___x_7187_ == 0 {
                    lean_dec_ref(v_es_7181_);
                    lean_dec_ref(v_f_7173_);
                    if v_isShared_7184_ == 0 {
                        lean_ctor_set_tag(v___x_7183_, 1);
                        lean_ctor_set(v___x_7183_, 0, v_x_7175_);
                        v___x_7189_ = v___x_7183_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7191_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7191_, 0, v_x_7175_);
                        v___x_7189_ = v_reuseFailAlloc_7191_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7192_ = lean_nat_dec_le(v___x_7186_, v___x_7186_);
                    if v___x_7192_ == 0 {
                        if v___x_7187_ == 0 {
                            lean_dec_ref(v_es_7181_);
                            lean_dec_ref(v_f_7173_);
                            if v_isShared_7184_ == 0 {
                                lean_ctor_set_tag(v___x_7183_, 1);
                                lean_ctor_set(v___x_7183_, 0, v_x_7175_);
                                v___x_7194_ = v___x_7183_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_7196_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7196_, 0, v_x_7175_);
                                v___x_7194_ = v_reuseFailAlloc_7196_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7183_);
                            v___x_7197_ = 0usize;
                            v___x_7198_ = lean_usize_of_nat(v___x_7186_);
                            v___x_7199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_7173_, v_es_7181_, v___x_7197_, v___x_7198_, v_x_7175_, v___y_7176_, v___y_7177_, v___y_7178_, v___y_7179_);
                            lean_dec_ref(v_es_7181_);
                            return v___x_7199_;
                        }
                    } else {
                        lean_del_object(v___x_7183_);
                        v___x_7200_ = 0usize;
                        v___x_7201_ = lean_usize_of_nat(v___x_7186_);
                        v___x_7202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_7173_, v_es_7181_, v___x_7200_, v___x_7201_, v_x_7175_, v___y_7176_, v___y_7177_, v___y_7178_, v___y_7179_);
                        lean_dec_ref(v_es_7181_);
                        return v___x_7202_;
                    }
                }
            }
            2 => {
                v___x_7190_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7190_, 0, v___x_7189_);
                return v___x_7190_;
            }
            3 => {
                v___x_7195_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7195_, 0, v___x_7194_);
                return v___x_7195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(
    mut v_f_7208_: *mut LeanObject,
    mut v_as_7209_: *mut LeanObject,
    mut v_i_7210_: usize,
    mut v_stop_7211_: usize,
    mut v_b_7212_: *mut LeanObject,
    mut v___y_7213_: *mut LeanObject,
    mut v___y_7214_: *mut LeanObject,
    mut v___y_7215_: *mut LeanObject,
    mut v___y_7216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: usize = 0;
    let mut v___x_7221_: usize = 0;
    let mut v___y_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: u8 = 0;
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7227_ = lean_usize_dec_eq(v_i_7210_, v_stop_7211_);
                if v___x_7227_ == 0 {
                    v___x_7228_ = lean_array_uget_borrowed(v_as_7209_, v_i_7210_);
                    match lean_obj_tag(v___x_7228_) {
                        0 => {
                            v_key_7229_ = lean_ctor_get(v___x_7228_, 0);
                            v_val_7230_ = lean_ctor_get(v___x_7228_, 1);
                            lean_inc_ref(v_f_7208_);
                            lean_inc(v___y_7216_);
                            lean_inc_ref(v___y_7215_);
                            lean_inc(v___y_7214_);
                            lean_inc_ref(v___y_7213_);
                            lean_inc(v_val_7230_);
                            lean_inc(v_key_7229_);
                            v___x_7231_ = lean_apply_8(
                                v_f_7208_,
                                v_b_7212_,
                                v_key_7229_,
                                v_val_7230_,
                                v___y_7213_,
                                v___y_7214_,
                                v___y_7215_,
                                v___y_7216_,
                                lean_box(0),
                            );
                            v___y_7224_ = v___x_7231_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_7232_ = lean_ctor_get(v___x_7228_, 0);
                            lean_inc(v_node_7232_);
                            lean_inc_ref(v_f_7208_);
                            v___x_7233_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_7208_, v_node_7232_, v_b_7212_, v___y_7213_, v___y_7214_, v___y_7215_, v___y_7216_);
                            v___y_7224_ = v___x_7233_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_7219_ = v_b_7212_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_7208_);
                    v___x_7234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7234_, 0, v_b_7212_);
                    v___x_7235_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7235_, 0, v___x_7234_);
                    return v___x_7235_;
                }
            }
            1 => {
                v___x_7220_ = 1usize;
                v___x_7221_ = lean_usize_add(v_i_7210_, v___x_7220_);
                v_i_7210_ = v___x_7221_;
                v_b_7212_ = v_a_7219_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_7224_) == 0 {
                    v_a_7225_ = lean_ctor_get(v___y_7224_, 0);
                    if lean_obj_tag(v_a_7225_) == 0 {
                        lean_dec_ref(v_f_7208_);
                        return v___y_7224_;
                    } else {
                        lean_inc_ref(v_a_7225_);
                        lean_dec_ref_known(v___y_7224_, 1);
                        v_a_7226_ = lean_ctor_get(v_a_7225_, 0);
                        lean_inc(v_a_7226_);
                        lean_dec_ref_known(v_a_7225_, 1);
                        v_a_7219_ = v_a_7226_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_7208_);
                    return v___y_7224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_f_7236_: *mut LeanObject,
    mut v_as_7237_: *mut LeanObject,
    mut v_i_7238_: *mut LeanObject,
    mut v_stop_7239_: *mut LeanObject,
    mut v_b_7240_: *mut LeanObject,
    mut v___y_7241_: *mut LeanObject,
    mut v___y_7242_: *mut LeanObject,
    mut v___y_7243_: *mut LeanObject,
    mut v___y_7244_: *mut LeanObject,
    mut v___y_7245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7246_: usize = 0;
    let mut v_stop_boxed_7247_: usize = 0;
    let mut v_res_7248_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7246_ = lean_unbox_usize(v_i_7238_);
    lean_dec(v_i_7238_);
    v_stop_boxed_7247_ = lean_unbox_usize(v_stop_7239_);
    lean_dec(v_stop_7239_);
    v_res_7248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_7236_, v_as_7237_, v_i_boxed_7246_, v_stop_boxed_7247_, v_b_7240_, v___y_7241_, v___y_7242_, v___y_7243_, v___y_7244_);
    lean_dec(v___y_7244_);
    lean_dec_ref(v___y_7243_);
    lean_dec(v___y_7242_);
    lean_dec_ref(v___y_7241_);
    lean_dec_ref(v_as_7237_);
    return v_res_7248_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_f_7249_: *mut LeanObject,
    mut v_x_7250_: *mut LeanObject,
    mut v_x_7251_: *mut LeanObject,
    mut v___y_7252_: *mut LeanObject,
    mut v___y_7253_: *mut LeanObject,
    mut v___y_7254_: *mut LeanObject,
    mut v___y_7255_: *mut LeanObject,
    mut v___y_7256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7257_: *mut LeanObject = core::ptr::null_mut();
    v_res_7257_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_7249_, v_x_7250_, v_x_7251_, v___y_7252_, v___y_7253_, v___y_7254_, v___y_7255_);
    lean_dec(v___y_7255_);
    lean_dec_ref(v___y_7254_);
    lean_dec(v___y_7253_);
    lean_dec_ref(v___y_7252_);
    return v_res_7257_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(
    mut v_f_7258_: *mut LeanObject,
    mut v_s_7259_: *mut LeanObject,
    mut v_a_7260_: *mut LeanObject,
    mut v_b_7261_: *mut LeanObject,
    mut v___y_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
    mut v___y_7265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7272_: u8 = 0;
    let mut v_a_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7276_: u8 = 0;
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7283_: u8 = 0;
    let mut v_a_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7287_: u8 = 0;
    let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7294_: u8 = 0;
    let mut v_isSharedCheck_7295_: u8 = 0;
    let mut v_a_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7299_: u8 = 0;
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7267_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7267_, 0, v_a_7260_);
                lean_ctor_set(v___x_7267_, 1, v_b_7261_);
                lean_inc(v___y_7265_);
                lean_inc_ref(v___y_7264_);
                lean_inc(v___y_7263_);
                lean_inc_ref(v___y_7262_);
                v___x_7268_ = lean_apply_7(
                    v_f_7258_,
                    v___x_7267_,
                    v_s_7259_,
                    v___y_7262_,
                    v___y_7263_,
                    v___y_7264_,
                    v___y_7265_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_7268_) == 0 {
                    v_a_7269_ = lean_ctor_get(v___x_7268_, 0);
                    v_isSharedCheck_7295_ = (!lean_is_exclusive(v___x_7268_)) as u8;
                    if v_isSharedCheck_7295_ == 0 {
                        v___x_7271_ = v___x_7268_;
                        v_isShared_7272_ = v_isSharedCheck_7295_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7269_);
                        lean_dec(v___x_7268_);
                        v___x_7271_ = lean_box(0);
                        v_isShared_7272_ = v_isSharedCheck_7295_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7296_ = lean_ctor_get(v___x_7268_, 0);
                    v_isSharedCheck_7303_ = (!lean_is_exclusive(v___x_7268_)) as u8;
                    if v_isSharedCheck_7303_ == 0 {
                        v___x_7298_ = v___x_7268_;
                        v_isShared_7299_ = v_isSharedCheck_7303_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7296_);
                        lean_dec(v___x_7268_);
                        v___x_7298_ = lean_box(0);
                        v_isShared_7299_ = v_isSharedCheck_7303_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7269_) == 0 {
                    v_a_7273_ = lean_ctor_get(v_a_7269_, 0);
                    v_isSharedCheck_7283_ = (!lean_is_exclusive(v_a_7269_)) as u8;
                    if v_isSharedCheck_7283_ == 0 {
                        v___x_7275_ = v_a_7269_;
                        v_isShared_7276_ = v_isSharedCheck_7283_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7273_);
                        lean_dec(v_a_7269_);
                        v___x_7275_ = lean_box(0);
                        v_isShared_7276_ = v_isSharedCheck_7283_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7284_ = lean_ctor_get(v_a_7269_, 0);
                    v_isSharedCheck_7294_ = (!lean_is_exclusive(v_a_7269_)) as u8;
                    if v_isSharedCheck_7294_ == 0 {
                        v___x_7286_ = v_a_7269_;
                        v_isShared_7287_ = v_isSharedCheck_7294_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7284_);
                        lean_dec(v_a_7269_);
                        v___x_7286_ = lean_box(0);
                        v_isShared_7287_ = v_isSharedCheck_7294_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7276_ == 0 {
                    v___x_7278_ = v___x_7275_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7282_, 0, v_a_7273_);
                    v___x_7278_ = v_reuseFailAlloc_7282_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7272_ == 0 {
                    lean_ctor_set(v___x_7271_, 0, v___x_7278_);
                    v___x_7280_ = v___x_7271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7281_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7281_, 0, v___x_7278_);
                    v___x_7280_ = v_reuseFailAlloc_7281_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7280_;
            }
            5 => {
                if v_isShared_7287_ == 0 {
                    v___x_7289_ = v___x_7286_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7293_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7293_, 0, v_a_7284_);
                    v___x_7289_ = v_reuseFailAlloc_7293_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7272_ == 0 {
                    lean_ctor_set(v___x_7271_, 0, v___x_7289_);
                    v___x_7291_ = v___x_7271_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7292_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7292_, 0, v___x_7289_);
                    v___x_7291_ = v_reuseFailAlloc_7292_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7291_;
            }
            8 => {
                if v_isShared_7299_ == 0 {
                    v___x_7301_ = v___x_7298_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7302_, 0, v_a_7296_);
                    v___x_7301_ = v_reuseFailAlloc_7302_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(
    mut v_f_7304_: *mut LeanObject,
    mut v_s_7305_: *mut LeanObject,
    mut v_a_7306_: *mut LeanObject,
    mut v_b_7307_: *mut LeanObject,
    mut v___y_7308_: *mut LeanObject,
    mut v___y_7309_: *mut LeanObject,
    mut v___y_7310_: *mut LeanObject,
    mut v___y_7311_: *mut LeanObject,
    mut v___y_7312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7313_: *mut LeanObject = core::ptr::null_mut();
    v_res_7313_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_7304_, v_s_7305_, v_a_7306_, v_b_7307_, v___y_7308_, v___y_7309_, v___y_7310_, v___y_7311_);
    lean_dec(v___y_7311_);
    lean_dec_ref(v___y_7310_);
    lean_dec(v___y_7309_);
    lean_dec_ref(v___y_7308_);
    return v_res_7313_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(
    mut v_map_7314_: *mut LeanObject,
    mut v_init_7315_: *mut LeanObject,
    mut v_f_7316_: *mut LeanObject,
    mut v___y_7317_: *mut LeanObject,
    mut v___y_7318_: *mut LeanObject,
    mut v___y_7319_: *mut LeanObject,
    mut v___y_7320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7327_: u8 = 0;
    let mut v_a_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7332_: u8 = 0;
    let mut v_a_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7336_: u8 = 0;
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7322_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                lean_closure_set(v___f_7322_, 0, v_f_7316_);
                lean_inc_ref(v_map_7314_);
                v___x_7323_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_7322_, v_map_7314_, v_init_7315_, v___y_7317_, v___y_7318_, v___y_7319_, v___y_7320_);
                if lean_obj_tag(v___x_7323_) == 0 {
                    v_a_7324_ = lean_ctor_get(v___x_7323_, 0);
                    v_isSharedCheck_7332_ = (!lean_is_exclusive(v___x_7323_)) as u8;
                    if v_isSharedCheck_7332_ == 0 {
                        v___x_7326_ = v___x_7323_;
                        v_isShared_7327_ = v_isSharedCheck_7332_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7324_);
                        lean_dec(v___x_7323_);
                        v___x_7326_ = lean_box(0);
                        v_isShared_7327_ = v_isSharedCheck_7332_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7333_ = lean_ctor_get(v___x_7323_, 0);
                    v_isSharedCheck_7340_ = (!lean_is_exclusive(v___x_7323_)) as u8;
                    if v_isSharedCheck_7340_ == 0 {
                        v___x_7335_ = v___x_7323_;
                        v_isShared_7336_ = v_isSharedCheck_7340_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7333_);
                        lean_dec(v___x_7323_);
                        v___x_7335_ = lean_box(0);
                        v_isShared_7336_ = v_isSharedCheck_7340_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_7328_ = lean_ctor_get(v_a_7324_, 0);
                lean_inc(v_a_7328_);
                lean_dec(v_a_7324_);
                if v_isShared_7327_ == 0 {
                    lean_ctor_set(v___x_7326_, 0, v_a_7328_);
                    v___x_7330_ = v___x_7326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7331_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7331_, 0, v_a_7328_);
                    v___x_7330_ = v_reuseFailAlloc_7331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7330_;
            }
            3 => {
                if v_isShared_7336_ == 0 {
                    v___x_7338_ = v___x_7335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7339_, 0, v_a_7333_);
                    v___x_7338_ = v_reuseFailAlloc_7339_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(
    mut v_map_7341_: *mut LeanObject,
    mut v_init_7342_: *mut LeanObject,
    mut v_f_7343_: *mut LeanObject,
    mut v___y_7344_: *mut LeanObject,
    mut v___y_7345_: *mut LeanObject,
    mut v___y_7346_: *mut LeanObject,
    mut v___y_7347_: *mut LeanObject,
    mut v___y_7348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7349_: *mut LeanObject = core::ptr::null_mut();
    v_res_7349_ =
        l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(
            v_map_7341_,
            v_init_7342_,
            v_f_7343_,
            v___y_7344_,
            v___y_7345_,
            v___y_7346_,
            v___y_7347_,
        );
    lean_dec(v___y_7347_);
    lean_dec_ref(v___y_7346_);
    lean_dec(v___y_7345_);
    lean_dec_ref(v___y_7344_);
    lean_dec_ref(v_map_7341_);
    return v_res_7349_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(
    mut v___y_7350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_categories_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7366_: u8 = 0;
    let mut v___y_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tables_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadingTable_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trailingTable_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstTokens_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstTokens_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: u8 = 0;
    let mut v___x_7393_: u8 = 0;
    let mut v___x_7394_: usize = 0;
    let mut v___x_7395_: usize = 0;
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: usize = 0;
    let mut v___x_7398_: usize = 0;
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7400_: u8 = 0;
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7352_ = lean_st_ref_get(v___y_7350_);
                v_env_7353_ = lean_ctor_get(v___x_7352_, 0);
                lean_inc_ref_n(v_env_7353_, 2);
                lean_dec(v___x_7352_);
                v___x_7354_ = l_Lean_Parser_parserExtension;
                v_ext_7355_ = lean_ctor_get(v___x_7354_, 1);
                v_toEnvExtension_7356_ = lean_ctor_get(v_ext_7355_, 0);
                v_asyncMode_7357_ = lean_ctor_get(v_toEnvExtension_7356_, 2);
                v___x_7358_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
                v___x_7359_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_7358_,
                    v___x_7354_,
                    v_env_7353_,
                    v_asyncMode_7357_,
                );
                v_categories_7360_ = lean_ctor_get(v___x_7359_, 2);
                lean_inc_ref(v_categories_7360_);
                lean_dec(v___x_7359_);
                v___x_7361_ =
                    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1;
                v___x_7362_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_7360_, v___x_7361_);
                lean_dec_ref(v_categories_7360_);
                if lean_obj_tag(v___x_7362_) == 1 {
                    v_val_7363_ = lean_ctor_get(v___x_7362_, 0);
                    v_isSharedCheck_7400_ = (!lean_is_exclusive(v___x_7362_)) as u8;
                    if v_isSharedCheck_7400_ == 0 {
                        v___x_7365_ = v___x_7362_;
                        v_isShared_7366_ = v_isSharedCheck_7400_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7363_);
                        lean_dec(v___x_7362_);
                        v___x_7365_ = lean_box(0);
                        v_isShared_7366_ = v_isSharedCheck_7400_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7362_);
                    lean_dec_ref(v_env_7353_);
                    v___x_7401_ = lean_box(1);
                    v___x_7402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7402_, 0, v___x_7401_);
                    return v___x_7402_;
                }
            }
            1 => {
                v___x_7377_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
                v_toEnvExtension_7378_ = lean_ctor_get(v___x_7377_, 0);
                v_exportEntriesFn_7379_ = lean_ctor_get(v___x_7377_, 4);
                v_asyncMode_7380_ = lean_ctor_get(v_toEnvExtension_7378_, 2);
                v___x_7381_ = lean_box(1);
                v___x_7382_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2,
                );
                v___x_7383_ = lean_box(0);
                lean_inc_ref_n(v_env_7353_, 2);
                v___x_7384_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_7382_,
                        v_toEnvExtension_7378_,
                        v_env_7353_,
                        v_asyncMode_7380_,
                        v___x_7383_,
                    );
                v_importedEntries_7385_ = lean_ctor_get(v___x_7384_, 0);
                lean_inc_ref(v_importedEntries_7385_);
                lean_dec(v___x_7384_);
                v___x_7386_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_7381_,
                    v___x_7377_,
                    v_env_7353_,
                    v_asyncMode_7380_,
                    v___x_7383_,
                );
                lean_inc_ref(v_exportEntriesFn_7379_);
                v___x_7387_ = lean_apply_2(v_exportEntriesFn_7379_, v_env_7353_, v___x_7386_);
                v_exported_7388_ = lean_ctor_get(v___x_7387_, 0);
                lean_inc(v_exported_7388_);
                lean_dec_ref(v___x_7387_);
                v___x_7389_ = lean_array_push(v_importedEntries_7385_, v_exported_7388_);
                v___x_7390_ = lean_unsigned_to_nat(0);
                v___x_7391_ = lean_array_get_size(v___x_7389_);
                v___x_7392_ = lean_nat_dec_lt(v___x_7390_, v___x_7391_);
                if v___x_7392_ == 0 {
                    lean_dec_ref(v___x_7389_);
                    v___y_7368_ = v___x_7381_;
                    state = 2;
                    continue;
                } else {
                    v___x_7393_ = lean_nat_dec_le(v___x_7391_, v___x_7391_);
                    if v___x_7393_ == 0 {
                        if v___x_7392_ == 0 {
                            lean_dec_ref(v___x_7389_);
                            v___y_7368_ = v___x_7381_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7394_ = 0usize;
                            v___x_7395_ = lean_usize_of_nat(v___x_7391_);
                            v___x_7396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_7389_, v___x_7394_, v___x_7395_, v___x_7381_);
                            lean_dec_ref(v___x_7389_);
                            v___y_7368_ = v___x_7396_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_7397_ = 0usize;
                        v___x_7398_ = lean_usize_of_nat(v___x_7391_);
                        v___x_7399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_7389_, v___x_7397_, v___x_7398_, v___x_7381_);
                        lean_dec_ref(v___x_7389_);
                        v___y_7368_ = v___x_7399_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_tables_7369_ = lean_ctor_get(v_val_7363_, 2);
                v_leadingTable_7370_ = lean_ctor_get(v_tables_7369_, 0);
                v_trailingTable_7371_ = lean_ctor_get(v_tables_7369_, 2);
                lean_inc(v_trailingTable_7371_);
                lean_inc(v_leadingTable_7370_);
                lean_inc(v_val_7363_);
                v_firstTokens_7372_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_7363_, v_leadingTable_7370_, v___y_7368_);
                v_firstTokens_7373_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_7363_, v_trailingTable_7371_, v_firstTokens_7372_);
                if v_isShared_7366_ == 0 {
                    lean_ctor_set_tag(v___x_7365_, 0);
                    lean_ctor_set(v___x_7365_, 0, v_firstTokens_7373_);
                    v___x_7375_ = v___x_7365_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7376_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7376_, 0, v_firstTokens_7373_);
                    v___x_7375_ = v_reuseFailAlloc_7376_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(
    mut v___y_7403_: *mut LeanObject,
    mut v___y_7404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7405_: *mut LeanObject = core::ptr::null_mut();
    v_res_7405_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_7403_);
    lean_dec(v___y_7403_);
    return v_res_7405_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_allTacticDocs(
    mut v_includeUnnamed_7408_: u8,
    mut v_a_7409_: *mut LeanObject,
    mut v_a_7410_: *mut LeanObject,
    mut v_a_7411_: *mut LeanObject,
    mut v_a_7412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7429_: usize = 0;
    let mut v___x_7430_: usize = 0;
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7435_: u8 = 0;
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_categories_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kinds_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7456_: u8 = 0;
    let mut v_a_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7460_: u8 = 0;
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7414_ = lean_st_ref_get(v_a_7412_);
                v_env_7415_ = lean_ctor_get(v___x_7414_, 0);
                lean_inc_ref_n(v_env_7415_, 4);
                lean_dec(v___x_7414_);
                v___x_7416_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
                v_toEnvExtension_7417_ = lean_ctor_get(v___x_7416_, 0);
                v_exportEntriesFn_7418_ = lean_ctor_get(v___x_7416_, 4);
                v_asyncMode_7419_ = lean_ctor_get(v_toEnvExtension_7417_, 2);
                v___x_7420_ = lean_box(1);
                v___x_7421_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0,
                );
                v___x_7422_ = lean_box(0);
                v___x_7423_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_7421_,
                        v_toEnvExtension_7417_,
                        v_env_7415_,
                        v_asyncMode_7419_,
                        v___x_7422_,
                    );
                v_importedEntries_7424_ = lean_ctor_get(v___x_7423_, 0);
                lean_inc_ref(v_importedEntries_7424_);
                lean_dec(v___x_7423_);
                v___x_7425_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_7420_,
                    v___x_7416_,
                    v_env_7415_,
                    v_asyncMode_7419_,
                    v___x_7422_,
                );
                lean_inc_ref(v_exportEntriesFn_7418_);
                v___x_7426_ = lean_apply_2(v_exportEntriesFn_7418_, v_env_7415_, v___x_7425_);
                v_exported_7427_ = lean_ctor_get(v___x_7426_, 0);
                lean_inc(v_exported_7427_);
                lean_dec_ref(v___x_7426_);
                v___x_7428_ = lean_array_push(v_importedEntries_7424_, v_exported_7427_);
                v_sz_7429_ = lean_array_size(v___x_7428_);
                v___x_7430_ = 0usize;
                v___x_7431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_7428_, v_sz_7429_, v___x_7430_, v___x_7420_, v_a_7409_, v_a_7410_, v_a_7411_, v_a_7412_);
                lean_dec_ref(v___x_7428_);
                if lean_obj_tag(v___x_7431_) == 0 {
                    v_a_7432_ = lean_ctor_get(v___x_7431_, 0);
                    v_isSharedCheck_7456_ = (!lean_is_exclusive(v___x_7431_)) as u8;
                    if v_isSharedCheck_7456_ == 0 {
                        v___x_7434_ = v___x_7431_;
                        v_isShared_7435_ = v_isSharedCheck_7456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7432_);
                        lean_dec(v___x_7431_);
                        v___x_7434_ = lean_box(0);
                        v_isShared_7435_ = v_isSharedCheck_7456_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_7415_);
                    v_a_7457_ = lean_ctor_get(v___x_7431_, 0);
                    v_isSharedCheck_7464_ = (!lean_is_exclusive(v___x_7431_)) as u8;
                    if v_isSharedCheck_7464_ == 0 {
                        v___x_7459_ = v___x_7431_;
                        v_isShared_7460_ = v_isSharedCheck_7464_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7457_);
                        lean_dec(v___x_7431_);
                        v___x_7459_ = lean_box(0);
                        v_isShared_7460_ = v_isSharedCheck_7464_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7436_ = l_Lean_Parser_parserExtension;
                v_ext_7437_ = lean_ctor_get(v___x_7436_, 1);
                v_toEnvExtension_7438_ = lean_ctor_get(v_ext_7437_, 0);
                v_asyncMode_7439_ = lean_ctor_get(v_toEnvExtension_7438_, 2);
                v___x_7440_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
                lean_inc_ref(v_env_7415_);
                v___x_7441_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_7440_,
                    v___x_7436_,
                    v_env_7415_,
                    v_asyncMode_7439_,
                );
                v_categories_7442_ = lean_ctor_get(v___x_7441_, 2);
                lean_inc_ref(v_categories_7442_);
                lean_dec(v___x_7441_);
                v___x_7443_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0;
                v___x_7444_ =
                    l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1;
                v___x_7445_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_7442_, v___x_7444_);
                lean_dec_ref(v_categories_7442_);
                if lean_obj_tag(v___x_7445_) == 1 {
                    lean_del_object(v___x_7434_);
                    v_val_7446_ = lean_ctor_get(v___x_7445_, 0);
                    lean_inc(v_val_7446_);
                    lean_dec_ref_known(v___x_7445_, 1);
                    v___x_7447_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_7412_);
                    v_a_7448_ = lean_ctor_get(v___x_7447_, 0);
                    lean_inc(v_a_7448_);
                    lean_dec_ref(v___x_7447_);
                    v_kinds_7449_ = lean_ctor_get(v_val_7446_, 1);
                    lean_inc_ref(v_kinds_7449_);
                    lean_dec(v_val_7446_);
                    v___x_7450_ = lean_box((v_includeUnnamed_7408_) as usize);
                    v___f_7451_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        4,
                    );
                    lean_closure_set(v___f_7451_, 0, v_env_7415_);
                    lean_closure_set(v___f_7451_, 1, v_a_7432_);
                    lean_closure_set(v___f_7451_, 2, v_a_7448_);
                    lean_closure_set(v___f_7451_, 3, v___x_7450_);
                    v___x_7452_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_7449_, v___x_7443_, v___f_7451_, v_a_7409_, v_a_7410_, v_a_7411_, v_a_7412_);
                    lean_dec_ref(v_kinds_7449_);
                    return v___x_7452_;
                } else {
                    lean_dec(v___x_7445_);
                    lean_dec(v_a_7432_);
                    lean_dec_ref(v_env_7415_);
                    if v_isShared_7435_ == 0 {
                        lean_ctor_set(v___x_7434_, 0, v___x_7443_);
                        v___x_7454_ = v___x_7434_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7455_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7455_, 0, v___x_7443_);
                        v___x_7454_ = v_reuseFailAlloc_7455_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7454_;
            }
            3 => {
                if v_isShared_7460_ == 0 {
                    v___x_7462_ = v___x_7459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7463_, 0, v_a_7457_);
                    v___x_7462_ = v_reuseFailAlloc_7463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(
    mut v_includeUnnamed_7465_: *mut LeanObject,
    mut v_a_7466_: *mut LeanObject,
    mut v_a_7467_: *mut LeanObject,
    mut v_a_7468_: *mut LeanObject,
    mut v_a_7469_: *mut LeanObject,
    mut v_a_7470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeUnnamed_boxed_7471_: u8 = 0;
    let mut v_res_7472_: *mut LeanObject = core::ptr::null_mut();
    v_includeUnnamed_boxed_7471_ = (lean_unbox(v_includeUnnamed_7465_) as u8);
    v_res_7472_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(
        v_includeUnnamed_boxed_7471_,
        v_a_7466_,
        v_a_7467_,
        v_a_7468_,
        v_a_7469_,
    );
    lean_dec(v_a_7469_);
    lean_dec_ref(v_a_7468_);
    lean_dec(v_a_7467_);
    lean_dec_ref(v_a_7466_);
    return v_res_7472_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(
    mut v_as_7473_: *mut LeanObject,
    mut v_sz_7474_: usize,
    mut v_i_7475_: usize,
    mut v_b_7476_: *mut LeanObject,
    mut v___y_7477_: *mut LeanObject,
    mut v___y_7478_: *mut LeanObject,
    mut v___y_7479_: *mut LeanObject,
    mut v___y_7480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
    v___x_7482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_7473_, v_sz_7474_, v_i_7475_, v_b_7476_);
    return v___x_7482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(
    mut v_as_7483_: *mut LeanObject,
    mut v_sz_7484_: *mut LeanObject,
    mut v_i_7485_: *mut LeanObject,
    mut v_b_7486_: *mut LeanObject,
    mut v___y_7487_: *mut LeanObject,
    mut v___y_7488_: *mut LeanObject,
    mut v___y_7489_: *mut LeanObject,
    mut v___y_7490_: *mut LeanObject,
    mut v___y_7491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7492_: usize = 0;
    let mut v_i_boxed_7493_: usize = 0;
    let mut v_res_7494_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7492_ = lean_unbox_usize(v_sz_7484_);
    lean_dec(v_sz_7484_);
    v_i_boxed_7493_ = lean_unbox_usize(v_i_7485_);
    lean_dec(v_i_7485_);
    v_res_7494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_7483_, v_sz_boxed_7492_, v_i_boxed_7493_, v_b_7486_, v___y_7487_, v___y_7488_, v___y_7489_, v___y_7490_);
    lean_dec(v___y_7490_);
    lean_dec_ref(v___y_7489_);
    lean_dec(v___y_7488_);
    lean_dec_ref(v___y_7487_);
    lean_dec_ref(v_as_7483_);
    return v_res_7494_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(
    mut v___y_7495_: *mut LeanObject,
    mut v___y_7496_: *mut LeanObject,
    mut v___y_7497_: *mut LeanObject,
    mut v___y_7498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7500_: *mut LeanObject = core::ptr::null_mut();
    v___x_7500_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_7498_);
    return v___x_7500_;
}
pub unsafe fn l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(
    mut v___y_7501_: *mut LeanObject,
    mut v___y_7502_: *mut LeanObject,
    mut v___y_7503_: *mut LeanObject,
    mut v___y_7504_: *mut LeanObject,
    mut v___y_7505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7506_: *mut LeanObject = core::ptr::null_mut();
    v_res_7506_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_7501_, v___y_7502_, v___y_7503_, v___y_7504_);
    lean_dec(v___y_7504_);
    lean_dec_ref(v___y_7503_);
    lean_dec(v___y_7502_);
    lean_dec_ref(v___y_7501_);
    return v_res_7506_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(
    mut v_00_u03c3_7507_: *mut LeanObject,
    mut v_00_u03b2_7508_: *mut LeanObject,
    mut v_map_7509_: *mut LeanObject,
    mut v_init_7510_: *mut LeanObject,
    mut v_f_7511_: *mut LeanObject,
    mut v___y_7512_: *mut LeanObject,
    mut v___y_7513_: *mut LeanObject,
    mut v___y_7514_: *mut LeanObject,
    mut v___y_7515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    v___x_7517_ =
        l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(
            v_map_7509_,
            v_init_7510_,
            v_f_7511_,
            v___y_7512_,
            v___y_7513_,
            v___y_7514_,
            v___y_7515_,
        );
    return v___x_7517_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(
    mut v_00_u03c3_7518_: *mut LeanObject,
    mut v_00_u03b2_7519_: *mut LeanObject,
    mut v_map_7520_: *mut LeanObject,
    mut v_init_7521_: *mut LeanObject,
    mut v_f_7522_: *mut LeanObject,
    mut v___y_7523_: *mut LeanObject,
    mut v___y_7524_: *mut LeanObject,
    mut v___y_7525_: *mut LeanObject,
    mut v___y_7526_: *mut LeanObject,
    mut v___y_7527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7528_: *mut LeanObject = core::ptr::null_mut();
    v_res_7528_ =
        l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(
            v_00_u03c3_7518_,
            v_00_u03b2_7519_,
            v_map_7520_,
            v_init_7521_,
            v_f_7522_,
            v___y_7523_,
            v___y_7524_,
            v___y_7525_,
            v___y_7526_,
        );
    lean_dec(v___y_7526_);
    lean_dec_ref(v___y_7525_);
    lean_dec(v___y_7524_);
    lean_dec_ref(v___y_7523_);
    lean_dec_ref(v_map_7520_);
    return v_res_7528_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(
    mut v_map_7529_: *mut LeanObject,
    mut v_f_7530_: *mut LeanObject,
    mut v_init_7531_: *mut LeanObject,
    mut v___y_7532_: *mut LeanObject,
    mut v___y_7533_: *mut LeanObject,
    mut v___y_7534_: *mut LeanObject,
    mut v___y_7535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7537_: *mut LeanObject = core::ptr::null_mut();
    v___x_7537_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_7530_, v_map_7529_, v_init_7531_, v___y_7532_, v___y_7533_, v___y_7534_, v___y_7535_);
    return v___x_7537_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(
    mut v_map_7538_: *mut LeanObject,
    mut v_f_7539_: *mut LeanObject,
    mut v_init_7540_: *mut LeanObject,
    mut v___y_7541_: *mut LeanObject,
    mut v___y_7542_: *mut LeanObject,
    mut v___y_7543_: *mut LeanObject,
    mut v___y_7544_: *mut LeanObject,
    mut v___y_7545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7546_: *mut LeanObject = core::ptr::null_mut();
    v_res_7546_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_7538_, v_f_7539_, v_init_7540_, v___y_7541_, v___y_7542_, v___y_7543_, v___y_7544_);
    lean_dec(v___y_7544_);
    lean_dec_ref(v___y_7543_);
    lean_dec(v___y_7542_);
    lean_dec_ref(v___y_7541_);
    return v_res_7546_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(
    mut v_00_u03c3_7547_: *mut LeanObject,
    mut v_00_u03c3_7548_: *mut LeanObject,
    mut v_00_u03b2_7549_: *mut LeanObject,
    mut v_map_7550_: *mut LeanObject,
    mut v_f_7551_: *mut LeanObject,
    mut v_init_7552_: *mut LeanObject,
    mut v___y_7553_: *mut LeanObject,
    mut v___y_7554_: *mut LeanObject,
    mut v___y_7555_: *mut LeanObject,
    mut v___y_7556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7558_: *mut LeanObject = core::ptr::null_mut();
    v___x_7558_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_7551_, v_map_7550_, v_init_7552_, v___y_7553_, v___y_7554_, v___y_7555_, v___y_7556_);
    return v___x_7558_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(
    mut v_00_u03c3_7559_: *mut LeanObject,
    mut v_00_u03c3_7560_: *mut LeanObject,
    mut v_00_u03b2_7561_: *mut LeanObject,
    mut v_map_7562_: *mut LeanObject,
    mut v_f_7563_: *mut LeanObject,
    mut v_init_7564_: *mut LeanObject,
    mut v___y_7565_: *mut LeanObject,
    mut v___y_7566_: *mut LeanObject,
    mut v___y_7567_: *mut LeanObject,
    mut v___y_7568_: *mut LeanObject,
    mut v___y_7569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7570_: *mut LeanObject = core::ptr::null_mut();
    v_res_7570_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_7559_, v_00_u03c3_7560_, v_00_u03b2_7561_, v_map_7562_, v_f_7563_, v_init_7564_, v___y_7565_, v___y_7566_, v___y_7567_, v___y_7568_);
    lean_dec(v___y_7568_);
    lean_dec_ref(v___y_7567_);
    lean_dec(v___y_7566_);
    lean_dec_ref(v___y_7565_);
    return v_res_7570_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(
    mut v_00_u03c3_7571_: *mut LeanObject,
    mut v_00_u03c3_7572_: *mut LeanObject,
    mut v_00_u03b1_7573_: *mut LeanObject,
    mut v_00_u03b2_7574_: *mut LeanObject,
    mut v_f_7575_: *mut LeanObject,
    mut v_x_7576_: *mut LeanObject,
    mut v_x_7577_: *mut LeanObject,
    mut v___y_7578_: *mut LeanObject,
    mut v___y_7579_: *mut LeanObject,
    mut v___y_7580_: *mut LeanObject,
    mut v___y_7581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    v___x_7583_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_7575_, v_x_7576_, v_x_7577_, v___y_7578_, v___y_7579_, v___y_7580_, v___y_7581_);
    return v___x_7583_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03c3_7584_: *mut LeanObject,
    mut v_00_u03c3_7585_: *mut LeanObject,
    mut v_00_u03b1_7586_: *mut LeanObject,
    mut v_00_u03b2_7587_: *mut LeanObject,
    mut v_f_7588_: *mut LeanObject,
    mut v_x_7589_: *mut LeanObject,
    mut v_x_7590_: *mut LeanObject,
    mut v___y_7591_: *mut LeanObject,
    mut v___y_7592_: *mut LeanObject,
    mut v___y_7593_: *mut LeanObject,
    mut v___y_7594_: *mut LeanObject,
    mut v___y_7595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7596_: *mut LeanObject = core::ptr::null_mut();
    v_res_7596_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_7584_, v_00_u03c3_7585_, v_00_u03b1_7586_, v_00_u03b2_7587_, v_f_7588_, v_x_7589_, v_x_7590_, v___y_7591_, v___y_7592_, v___y_7593_, v___y_7594_);
    lean_dec(v___y_7594_);
    lean_dec_ref(v___y_7593_);
    lean_dec(v___y_7592_);
    lean_dec_ref(v___y_7591_);
    return v_res_7596_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(
    mut v_00_u03b1_7597_: *mut LeanObject,
    mut v_00_u03b2_7598_: *mut LeanObject,
    mut v_00_u03c3_7599_: *mut LeanObject,
    mut v_00_u03c3_7600_: *mut LeanObject,
    mut v_f_7601_: *mut LeanObject,
    mut v_as_7602_: *mut LeanObject,
    mut v_i_7603_: usize,
    mut v_stop_7604_: usize,
    mut v_b_7605_: *mut LeanObject,
    mut v___y_7606_: *mut LeanObject,
    mut v___y_7607_: *mut LeanObject,
    mut v___y_7608_: *mut LeanObject,
    mut v___y_7609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7611_: *mut LeanObject = core::ptr::null_mut();
    v___x_7611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_7601_, v_as_7602_, v_i_7603_, v_stop_7604_, v_b_7605_, v___y_7606_, v___y_7607_, v___y_7608_, v___y_7609_);
    return v___x_7611_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(
    mut v_00_u03b1_7612_: *mut LeanObject,
    mut v_00_u03b2_7613_: *mut LeanObject,
    mut v_00_u03c3_7614_: *mut LeanObject,
    mut v_00_u03c3_7615_: *mut LeanObject,
    mut v_f_7616_: *mut LeanObject,
    mut v_as_7617_: *mut LeanObject,
    mut v_i_7618_: *mut LeanObject,
    mut v_stop_7619_: *mut LeanObject,
    mut v_b_7620_: *mut LeanObject,
    mut v___y_7621_: *mut LeanObject,
    mut v___y_7622_: *mut LeanObject,
    mut v___y_7623_: *mut LeanObject,
    mut v___y_7624_: *mut LeanObject,
    mut v___y_7625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7626_: usize = 0;
    let mut v_stop_boxed_7627_: usize = 0;
    let mut v_res_7628_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7626_ = lean_unbox_usize(v_i_7618_);
    lean_dec(v_i_7618_);
    v_stop_boxed_7627_ = lean_unbox_usize(v_stop_7619_);
    lean_dec(v_stop_7619_);
    v_res_7628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_7612_, v_00_u03b2_7613_, v_00_u03c3_7614_, v_00_u03c3_7615_, v_f_7616_, v_as_7617_, v_i_boxed_7626_, v_stop_boxed_7627_, v_b_7620_, v___y_7621_, v___y_7622_, v___y_7623_, v___y_7624_);
    lean_dec(v___y_7624_);
    lean_dec_ref(v___y_7623_);
    lean_dec(v___y_7622_);
    lean_dec_ref(v___y_7621_);
    lean_dec_ref(v_as_7617_);
    return v_res_7628_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(
    mut v_00_u03c3_7629_: *mut LeanObject,
    mut v_00_u03c3_7630_: *mut LeanObject,
    mut v_00_u03b1_7631_: *mut LeanObject,
    mut v_00_u03b2_7632_: *mut LeanObject,
    mut v_f_7633_: *mut LeanObject,
    mut v_keys_7634_: *mut LeanObject,
    mut v_vals_7635_: *mut LeanObject,
    mut v_heq_7636_: *mut LeanObject,
    mut v_i_7637_: *mut LeanObject,
    mut v_acc_7638_: *mut LeanObject,
    mut v___y_7639_: *mut LeanObject,
    mut v___y_7640_: *mut LeanObject,
    mut v___y_7641_: *mut LeanObject,
    mut v___y_7642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    v___x_7644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_7633_, v_keys_7634_, v_vals_7635_, v_i_7637_, v_acc_7638_, v___y_7639_, v___y_7640_, v___y_7641_, v___y_7642_);
    return v___x_7644_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03c3_7645_: *mut LeanObject,
    mut v_00_u03c3_7646_: *mut LeanObject,
    mut v_00_u03b1_7647_: *mut LeanObject,
    mut v_00_u03b2_7648_: *mut LeanObject,
    mut v_f_7649_: *mut LeanObject,
    mut v_keys_7650_: *mut LeanObject,
    mut v_vals_7651_: *mut LeanObject,
    mut v_heq_7652_: *mut LeanObject,
    mut v_i_7653_: *mut LeanObject,
    mut v_acc_7654_: *mut LeanObject,
    mut v___y_7655_: *mut LeanObject,
    mut v___y_7656_: *mut LeanObject,
    mut v___y_7657_: *mut LeanObject,
    mut v___y_7658_: *mut LeanObject,
    mut v___y_7659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7660_: *mut LeanObject = core::ptr::null_mut();
    v_res_7660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_7645_, v_00_u03c3_7646_, v_00_u03b1_7647_, v_00_u03b2_7648_, v_f_7649_, v_keys_7650_, v_vals_7651_, v_heq_7652_, v_i_7653_, v_acc_7654_, v___y_7655_, v___y_7656_, v___y_7657_, v___y_7658_);
    lean_dec(v___y_7658_);
    lean_dec_ref(v___y_7657_);
    lean_dec(v___y_7656_);
    lean_dec_ref(v___y_7655_);
    lean_dec_ref(v_vals_7651_);
    lean_dec_ref(v_keys_7650_);
    return v_res_7660_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Doc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Doc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Doc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Doc(builtin);
}
