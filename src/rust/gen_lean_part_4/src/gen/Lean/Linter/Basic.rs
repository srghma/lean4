// Lean compiler output
// Module: Lean.Linter.Basic
// Imports: Lean.Linter.Init Lean.Elab.Command
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNatLit_x3f, l_Lean_Syntax_isStrLit_x3f};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_getKind,
    lean_erase_macro_scopes,
};
use crate::r#gen::Init::Syntax::l_Lean_Syntax_setArgs;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::KVMap::l_Lean_DataValue_sameCtor;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_getOptionDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_withScope___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::SetOption::l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__0_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 96, 32, 99, 111, 109, 109, 97, 110, 100, 58, 32, 84, 104, 101, 32, 111, 112, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__2_value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 99, 111, 110, 102, 105, 103, 117, 114, 101, 100, 32, 117, 115, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [10, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [10, 98, 117, 116, 32, 116, 104, 101, 32, 111, 112, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__4_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [96, 32, 101, 120, 112, 101, 99, 116, 115, 32, 97, 32, 118, 97, 108, 117, 101, 32, 111, 102, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__6_value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 118, 97, 108, 117, 101, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 58, 32, 84, 104, 101, 32, 118, 97, 108, 117, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__8_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__10_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__12_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__13_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__12_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__14_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__15_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__16_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__16_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__0_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 101, 116, 95, 111, 112, 116, 105,
        111, 110, 32, 118, 97, 108, 117, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__2_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        96, 59, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 108, 105, 116, 101, 114, 97,
        108, 32, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_withSetOptionIn___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_withSetOptionIn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_withSetOptionIn___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_withSetOptionIn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_withSetOptionIn___closed__2_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_withSetOptionIn___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_withSetOptionIn___closed__3_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [105, 110, 0],
    };
static mut l_Lean_withSetOptionIn___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_withSetOptionIn___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_withSetOptionIn___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_withSetOptionIn___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__2_value)
                as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_withSetOptionIn___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__3_value)
                as *mut leanh::LeanObject,
            745669085263777601 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_withSetOptionIn___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_withSetOptionIn___closed__5_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_withSetOptionIn___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__5_value) as *mut leanh::LeanObject;
static l_Lean_withSetOptionIn___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_withSetOptionIn___closed__6_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_withSetOptionIn___closed__6_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__6_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__2_value)
                as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_withSetOptionIn___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__6_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__5_value)
                as *mut leanh::LeanObject,
            14305216472754282456 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_withSetOptionIn___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withSetOptionIn___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2___redArg(
    mut v_t_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_859_: u8 = 0;
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v_enabled_877_: u8 = 0;
    let mut v_assignment_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_883_: u8 = 0;
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_894_: u8 = 0;
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_857_ = lean_st_ref_get(v___y_855_);
                v_infoState_858_ = leanh::lean_ctor_get(v___x_857_, 8);
                leanh::lean_inc_ref(v_infoState_858_);
                leanh::lean_dec(v___x_857_);
                v_enabled_859_ = leanh::lean_ctor_get_uint8(
                    v_infoState_858_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_858_);
                if v_enabled_859_ == 0 {
                    leanh::lean_dec_ref(v_t_854_);
                    v___x_860_ = leanh::lean_box(0);
                    v___x_861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_861_, 0, v___x_860_);
                    return v___x_861_;
                } else {
                    v___x_862_ = lean_st_ref_take(v___y_855_);
                    v_infoState_863_ = leanh::lean_ctor_get(v___x_862_, 8);
                    v_env_864_ = leanh::lean_ctor_get(v___x_862_, 0);
                    v_messages_865_ = leanh::lean_ctor_get(v___x_862_, 1);
                    v_scopes_866_ = leanh::lean_ctor_get(v___x_862_, 2);
                    v_usedQuotCtxts_867_ = leanh::lean_ctor_get(v___x_862_, 3);
                    v_nextMacroScope_868_ = leanh::lean_ctor_get(v___x_862_, 4);
                    v_maxRecDepth_869_ = leanh::lean_ctor_get(v___x_862_, 5);
                    v_ngen_870_ = leanh::lean_ctor_get(v___x_862_, 6);
                    v_auxDeclNGen_871_ = leanh::lean_ctor_get(v___x_862_, 7);
                    v_traceState_872_ = leanh::lean_ctor_get(v___x_862_, 9);
                    v_snapshotTasks_873_ = leanh::lean_ctor_get(v___x_862_, 10);
                    v_isSharedCheck_895_ = (!leanh::lean_is_exclusive(v___x_862_)) as u8;
                    if v_isSharedCheck_895_ == 0 {
                        v___x_875_ = v___x_862_;
                        v_isShared_876_ = v_isSharedCheck_895_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_873_);
                        leanh::lean_inc(v_traceState_872_);
                        leanh::lean_inc(v_infoState_863_);
                        leanh::lean_inc(v_auxDeclNGen_871_);
                        leanh::lean_inc(v_ngen_870_);
                        leanh::lean_inc(v_maxRecDepth_869_);
                        leanh::lean_inc(v_nextMacroScope_868_);
                        leanh::lean_inc(v_usedQuotCtxts_867_);
                        leanh::lean_inc(v_scopes_866_);
                        leanh::lean_inc(v_messages_865_);
                        leanh::lean_inc(v_env_864_);
                        leanh::lean_dec(v___x_862_);
                        v___x_875_ = leanh::lean_box(0);
                        v_isShared_876_ = v_isSharedCheck_895_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_877_ = leanh::lean_ctor_get_uint8(
                    v_infoState_863_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_878_ = leanh::lean_ctor_get(v_infoState_863_, 0);
                v_lazyAssignment_879_ = leanh::lean_ctor_get(v_infoState_863_, 1);
                v_trees_880_ = leanh::lean_ctor_get(v_infoState_863_, 2);
                v_isSharedCheck_894_ = (!leanh::lean_is_exclusive(v_infoState_863_)) as u8;
                if v_isSharedCheck_894_ == 0 {
                    v___x_882_ = v_infoState_863_;
                    v_isShared_883_ = v_isSharedCheck_894_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_trees_880_);
                    leanh::lean_inc(v_lazyAssignment_879_);
                    leanh::lean_inc(v_assignment_878_);
                    leanh::lean_dec(v_infoState_863_);
                    v___x_882_ = leanh::lean_box(0);
                    v_isShared_883_ = v_isSharedCheck_894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_884_ = l_Lean_PersistentArray_push___redArg(v_trees_880_, v_t_854_);
                if v_isShared_883_ == 0 {
                    leanh::lean_ctor_set(v___x_882_, 2, v___x_884_);
                    v___x_886_ = v___x_882_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_893_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_893_, 0, v_assignment_878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_893_, 1, v_lazyAssignment_879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_893_, 2, v___x_884_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_893_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_877_,
                    );
                    v___x_886_ = v_reuseFailAlloc_893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_876_ == 0 {
                    leanh::lean_ctor_set(v___x_875_, 8, v___x_886_);
                    v___x_888_ = v___x_875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_env_864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 1, v_messages_865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 2, v_scopes_866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 3, v_usedQuotCtxts_867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 4, v_nextMacroScope_868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 5, v_maxRecDepth_869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 6, v_ngen_870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 7, v_auxDeclNGen_871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 8, v___x_886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 9, v_traceState_872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 10, v_snapshotTasks_873_);
                    v___x_888_ = v_reuseFailAlloc_892_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_889_ = lean_st_ref_set(v___y_855_, v___x_888_);
                v___x_890_ = leanh::lean_box(0);
                v___x_891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_891_, 0, v___x_890_);
                return v___x_891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_t_896_: *mut leanh::LeanObject,
    mut v___y_897_: *mut leanh::LeanObject,
    mut v___y_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2___redArg(v_t_896_, v___y_897_);
    leanh::lean_dec(v___y_897_);
    return v_res_899_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = leanh::lean_unsigned_to_nat(32);
    v___x_901_ = lean_mk_empty_array_with_capacity(v___x_900_);
    v___x_902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_902_, 0, v___x_901_);
    return v___x_902_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_903_: usize = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = 5usize;
    v___x_904_ = leanh::lean_unsigned_to_nat(0);
    v___x_905_ = leanh::lean_unsigned_to_nat(32);
    v___x_906_ = lean_mk_empty_array_with_capacity(v___x_905_);
    v___x_907_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__0);
    v___x_908_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_908_, 0, v___x_907_);
    leanh::lean_ctor_set(v___x_908_, 1, v___x_906_);
    leanh::lean_ctor_set(v___x_908_, 2, v___x_904_);
    leanh::lean_ctor_set(v___x_908_, 3, v___x_904_);
    leanh::lean_ctor_set_usize(v___x_908_, 4, v___x_903_);
    return v___x_908_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1(
    mut v_t_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
    mut v___y_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_915_: u8 = 0;
    v___x_913_ = lean_st_ref_get(v___y_911_);
    v_infoState_914_ = leanh::lean_ctor_get(v___x_913_, 8);
    leanh::lean_inc_ref(v_infoState_914_);
    leanh::lean_dec(v___x_913_);
    v_enabled_915_ = leanh::lean_ctor_get_uint8(
        v_infoState_914_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    leanh::lean_dec_ref(v_infoState_914_);
    if v_enabled_915_ == 0 {
        let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_t_909_);
        v___x_916_ = leanh::lean_box(0);
        v___x_917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_917_, 0, v___x_916_);
        return v___x_917_;
    } else {
        let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_918_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___closed__1);
        v___x_919_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_919_, 0, v_t_909_);
        leanh::lean_ctor_set(v___x_919_, 1, v___x_918_);
        v___x_920_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2___redArg(v___x_919_, v___y_911_);
        return v___x_920_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1___boxed(
    mut v_t_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1(v_t_921_, v___y_922_, v___y_923_);
    leanh::lean_dec(v___y_923_);
    leanh::lean_dec_ref(v___y_922_);
    return v_res_925_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_926_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__0);
    v___x_928_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_928_, 0, v___x_927_);
    return v___x_928_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_929_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1);
    v___x_930_ = leanh::lean_unsigned_to_nat(0);
    v___x_931_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_931_, 0, v___x_930_);
    leanh::lean_ctor_set(v___x_931_, 1, v___x_930_);
    leanh::lean_ctor_set(v___x_931_, 2, v___x_930_);
    leanh::lean_ctor_set(v___x_931_, 3, v___x_930_);
    leanh::lean_ctor_set(v___x_931_, 4, v___x_929_);
    leanh::lean_ctor_set(v___x_931_, 5, v___x_929_);
    leanh::lean_ctor_set(v___x_931_, 6, v___x_929_);
    leanh::lean_ctor_set(v___x_931_, 7, v___x_929_);
    leanh::lean_ctor_set(v___x_931_, 8, v___x_929_);
    leanh::lean_ctor_set(v___x_931_, 9, v___x_929_);
    return v___x_931_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = leanh::lean_unsigned_to_nat(32);
    v___x_933_ = lean_mk_empty_array_with_capacity(v___x_932_);
    v___x_934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_934_, 0, v___x_933_);
    return v___x_934_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_935_: usize = 0;
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_935_ = 5usize;
    v___x_936_ = leanh::lean_unsigned_to_nat(0);
    v___x_937_ = leanh::lean_unsigned_to_nat(32);
    v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
    v___x_939_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__3);
    v___x_940_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_940_, 0, v___x_939_);
    leanh::lean_ctor_set(v___x_940_, 1, v___x_938_);
    leanh::lean_ctor_set(v___x_940_, 2, v___x_936_);
    leanh::lean_ctor_set(v___x_940_, 3, v___x_936_);
    leanh::lean_ctor_set_usize(v___x_940_, 4, v___x_935_);
    return v___x_940_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = leanh::lean_box(1);
    v___x_942_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__4);
    v___x_943_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__1);
    v___x_944_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_944_, 0, v___x_943_);
    leanh::lean_ctor_set(v___x_944_, 1, v___x_942_);
    leanh::lean_ctor_set(v___x_944_, 2, v___x_941_);
    return v___x_944_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg(
    mut v_msgData_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_948_ = lean_st_ref_get(v___y_946_);
    v_env_949_ = leanh::lean_ctor_get(v___x_948_, 0);
    leanh::lean_inc_ref(v_env_949_);
    leanh::lean_dec(v___x_948_);
    v___x_950_ = lean_st_ref_get(v___y_946_);
    v_scopes_951_ = leanh::lean_ctor_get(v___x_950_, 2);
    leanh::lean_inc(v_scopes_951_);
    leanh::lean_dec(v___x_950_);
    v___x_952_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_953_ = l_List_head_x21___redArg(v___x_952_, v_scopes_951_);
    leanh::lean_dec(v_scopes_951_);
    v_opts_954_ = leanh::lean_ctor_get(v___x_953_, 1);
    leanh::lean_inc_ref(v_opts_954_);
    leanh::lean_dec(v___x_953_);
    v___x_955_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__2);
    v___x_956_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___closed__5);
    v___x_957_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_957_, 0, v_env_949_);
    leanh::lean_ctor_set(v___x_957_, 1, v___x_955_);
    leanh::lean_ctor_set(v___x_957_, 2, v___x_956_);
    leanh::lean_ctor_set(v___x_957_, 3, v_opts_954_);
    v___x_958_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_958_, 0, v___x_957_);
    leanh::lean_ctor_set(v___x_958_, 1, v_msgData_945_);
    v___x_959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_959_, 0, v___x_958_);
    return v___x_959_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_msgData_960_: *mut leanh::LeanObject,
    mut v___y_961_: *mut leanh::LeanObject,
    mut v___y_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_963_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg(v_msgData_960_, v___y_961_);
    leanh::lean_dec(v___y_961_);
    return v_res_963_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__8(
    mut v_opts_964_: *mut leanh::LeanObject,
    mut v_opt_965_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_966_ = leanh::lean_ctor_get(v_opt_965_, 0);
    v_defValue_967_ = leanh::lean_ctor_get(v_opt_965_, 1);
    v_map_968_ = leanh::lean_ctor_get(v_opts_964_, 0);
    v___x_969_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_968_,
            v_name_966_,
        );
    if leanh::lean_obj_tag(v___x_969_) == 0 {
        let mut v___x_970_: u8 = 0;
        v___x_970_ = (leanh::lean_unbox(v_defValue_967_) as u8);
        return v___x_970_;
    } else {
        let mut v_val_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_971_ = leanh::lean_ctor_get(v___x_969_, 0);
        leanh::lean_inc(v_val_971_);
        leanh::lean_dec_ref_known(v___x_969_, 1);
        if leanh::lean_obj_tag(v_val_971_) == 1 {
            let mut v_v_972_: u8 = 0;
            v_v_972_ = leanh::lean_ctor_get_uint8(v_val_971_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_971_, 0);
            return v_v_972_;
        } else {
            let mut v___x_973_: u8 = 0;
            leanh::lean_dec(v_val_971_);
            v___x_973_ = (leanh::lean_unbox(v_defValue_967_) as u8);
            return v___x_973_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__8___boxed(
    mut v_opts_974_: *mut leanh::LeanObject,
    mut v_opt_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_976_: u8 = 0;
    let mut v_r_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_976_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__8(v_opts_974_, v_opt_975_);
    leanh::lean_dec_ref(v_opt_975_);
    leanh::lean_dec_ref(v_opts_974_);
    v_r_977_ = leanh::lean_box((v_res_976_) as usize);
    return v_r_977_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = leanh::lean_box(1);
    v___x_979_ = l_Lean_MessageData_ofFormat(v___x_978_);
    return v___x_979_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__2;
    v___x_984_ = l_Lean_MessageData_ofFormat(v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9(
    mut v_x_985_: *mut leanh::LeanObject,
    mut v_x_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v_before_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_unused_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_986_) == 0 {
                    return v_x_985_;
                } else {
                    v_head_987_ = leanh::lean_ctor_get(v_x_986_, 0);
                    v_tail_988_ = leanh::lean_ctor_get(v_x_986_, 1);
                    v_isSharedCheck_1010_ = (!leanh::lean_is_exclusive(v_x_986_)) as u8;
                    if v_isSharedCheck_1010_ == 0 {
                        v___x_990_ = v_x_986_;
                        v_isShared_991_ = v_isSharedCheck_1010_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_988_);
                        leanh::lean_inc(v_head_987_);
                        leanh::lean_dec(v_x_986_);
                        v___x_990_ = leanh::lean_box(0);
                        v_isShared_991_ = v_isSharedCheck_1010_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_992_ = leanh::lean_ctor_get(v_head_987_, 0);
                v_isSharedCheck_1008_ = (!leanh::lean_is_exclusive(v_head_987_)) as u8;
                if v_isSharedCheck_1008_ == 0 {
                    v_unused_1009_ = leanh::lean_ctor_get(v_head_987_, 1);
                    leanh::lean_dec(v_unused_1009_);
                    v___x_994_ = v_head_987_;
                    v_isShared_995_ = v_isSharedCheck_1008_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_992_);
                    leanh::lean_dec(v_head_987_);
                    v___x_994_ = leanh::lean_box(0);
                    v_isShared_995_ = v_isSharedCheck_1008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_996_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0);
                if v_isShared_995_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_994_, 7);
                    leanh::lean_ctor_set(v___x_994_, 1, v___x_996_);
                    leanh::lean_ctor_set(v___x_994_, 0, v_x_985_);
                    v___x_998_ = v___x_994_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_x_985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_996_);
                    v___x_998_ = v_reuseFailAlloc_1007_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_999_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__3);
                if v_isShared_991_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_990_, 7);
                    leanh::lean_ctor_set(v___x_990_, 1, v___x_999_);
                    leanh::lean_ctor_set(v___x_990_, 0, v___x_998_);
                    v___x_1001_ = v___x_990_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1006_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_999_);
                    v___x_1001_ = v_reuseFailAlloc_1006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1002_ = l_Lean_MessageData_ofSyntax(v_before_992_);
                v___x_1003_ = l_Lean_indentD(v___x_1002_);
                v___x_1004_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1004_, 0, v___x_1001_);
                leanh::lean_ctor_set(v___x_1004_, 1, v___x_1003_);
                v_x_985_ = v___x_1004_;
                v_x_986_ = v_tail_988_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__1;
    v___x_1015_ = l_Lean_MessageData_ofFormat(v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg(
    mut v_msgData_1016_: *mut leanh::LeanObject,
    mut v_macroStack_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1033_: u8 = 0;
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_unused_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1020_ = lean_st_ref_get(v___y_1018_);
                v_scopes_1021_ = leanh::lean_ctor_get(v___x_1020_, 2);
                leanh::lean_inc(v_scopes_1021_);
                leanh::lean_dec(v___x_1020_);
                v___x_1022_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1023_ = l_List_head_x21___redArg(v___x_1022_, v_scopes_1021_);
                leanh::lean_dec(v_scopes_1021_);
                v_opts_1024_ = leanh::lean_ctor_get(v___x_1023_, 1);
                leanh::lean_inc_ref(v_opts_1024_);
                leanh::lean_dec(v___x_1023_);
                v___x_1025_ = l_Lean_Elab_pp_macroStack;
                v___x_1026_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__8(v_opts_1024_, v___x_1025_);
                leanh::lean_dec_ref(v_opts_1024_);
                if v___x_1026_ == 0 {
                    leanh::lean_dec(v_macroStack_1017_);
                    v___x_1027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1027_, 0, v_msgData_1016_);
                    return v___x_1027_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_1017_) == 0 {
                        v___x_1028_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1028_, 0, v_msgData_1016_);
                        return v___x_1028_;
                    } else {
                        v_head_1029_ = leanh::lean_ctor_get(v_macroStack_1017_, 0);
                        leanh::lean_inc(v_head_1029_);
                        v_after_1030_ = leanh::lean_ctor_get(v_head_1029_, 1);
                        v_isSharedCheck_1045_ =
                            (!leanh::lean_is_exclusive(v_head_1029_)) as u8;
                        if v_isSharedCheck_1045_ == 0 {
                            v_unused_1046_ = leanh::lean_ctor_get(v_head_1029_, 0);
                            leanh::lean_dec(v_unused_1046_);
                            v___x_1032_ = v_head_1029_;
                            v_isShared_1033_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_1030_);
                            leanh::lean_dec(v_head_1029_);
                            v___x_1032_ = leanh::lean_box(0);
                            v_isShared_1033_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1034_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9___closed__0);
                if v_isShared_1033_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1032_, 7);
                    leanh::lean_ctor_set(v___x_1032_, 1, v___x_1034_);
                    leanh::lean_ctor_set(v___x_1032_, 0, v_msgData_1016_);
                    v___x_1036_ = v___x_1032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_msgData_1016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1034_);
                    v___x_1036_ = v_reuseFailAlloc_1044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1037_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___closed__2);
                v___x_1038_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1038_, 0, v___x_1036_);
                leanh::lean_ctor_set(v___x_1038_, 1, v___x_1037_);
                v___x_1039_ = l_Lean_MessageData_ofSyntax(v_after_1030_);
                v___x_1040_ = l_Lean_indentD(v___x_1039_);
                v_msgData_1041_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_1041_, 0, v___x_1038_);
                leanh::lean_ctor_set(v_msgData_1041_, 1, v___x_1040_);
                v___x_1042_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5_spec__9(v_msgData_1041_, v_macroStack_1017_);
                v___x_1043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1043_, 0, v___x_1042_);
                return v___x_1043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_msgData_1047_: *mut leanh::LeanObject,
    mut v_macroStack_1048_: *mut leanh::LeanObject,
    mut v___y_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg(v_msgData_1047_, v_macroStack_1048_, v___y_1049_);
    leanh::lean_dec(v___y_1049_);
    return v_res_1051_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg(
    mut v_msg_1052_: *mut leanh::LeanObject,
    mut v___y_1053_: *mut leanh::LeanObject,
    mut v___y_1054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut v_a_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1056_ = l_Lean_Elab_Command_getRef___redArg(v___y_1053_);
                if leanh::lean_obj_tag(v___x_1056_) == 0 {
                    v_a_1057_ = leanh::lean_ctor_get(v___x_1056_, 0);
                    leanh::lean_inc(v_a_1057_);
                    leanh::lean_dec_ref_known(v___x_1056_, 1);
                    v_macroStack_1058_ = leanh::lean_ctor_get(v___y_1053_, 4);
                    v___x_1059_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg(v_msg_1052_, v___y_1054_);
                    v_a_1060_ = leanh::lean_ctor_get(v___x_1059_, 0);
                    leanh::lean_inc(v_a_1060_);
                    leanh::lean_dec_ref(v___x_1059_);
                    v___x_1061_ = l_Lean_Elab_getBetterRef(v_a_1057_, v_macroStack_1058_);
                    leanh::lean_dec(v_a_1057_);
                    leanh::lean_inc(v_macroStack_1058_);
                    v___x_1062_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg(v_a_1060_, v_macroStack_1058_, v___y_1054_);
                    v_a_1063_ = leanh::lean_ctor_get(v___x_1062_, 0);
                    v_isSharedCheck_1071_ = (!leanh::lean_is_exclusive(v___x_1062_)) as u8;
                    if v_isSharedCheck_1071_ == 0 {
                        v___x_1065_ = v___x_1062_;
                        v_isShared_1066_ = v_isSharedCheck_1071_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1063_);
                        leanh::lean_dec(v___x_1062_);
                        v___x_1065_ = leanh::lean_box(0);
                        v_isShared_1066_ = v_isSharedCheck_1071_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_1052_);
                    v_a_1072_ = leanh::lean_ctor_get(v___x_1056_, 0);
                    v_isSharedCheck_1079_ = (!leanh::lean_is_exclusive(v___x_1056_)) as u8;
                    if v_isSharedCheck_1079_ == 0 {
                        v___x_1074_ = v___x_1056_;
                        v_isShared_1075_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1072_);
                        leanh::lean_dec(v___x_1056_);
                        v___x_1074_ = leanh::lean_box(0);
                        v_isShared_1075_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1067_, 0, v___x_1061_);
                leanh::lean_ctor_set(v___x_1067_, 1, v_a_1063_);
                if v_isShared_1066_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1065_, 1);
                    leanh::lean_ctor_set(v___x_1065_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1069_;
            }
            3 => {
                if v_isShared_1075_ == 0 {
                    v___x_1077_ = v___x_1074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg___boxed(
    mut v_msg_1080_: *mut leanh::LeanObject,
    mut v___y_1081_: *mut leanh::LeanObject,
    mut v___y_1082_: *mut leanh::LeanObject,
    mut v___y_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg(v_msg_1080_, v___y_1081_, v___y_1082_);
    leanh::lean_dec(v___y_1082_);
    leanh::lean_dec_ref(v___y_1081_);
    return v_res_1084_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__0;
    v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
    return v___x_1087_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__2;
    v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
    return v___x_1090_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg(
    mut v_optionName_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__1_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__1);
    v___x_1096_ = l_Lean_MessageData_ofName(v_optionName_1091_);
    v___x_1097_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1097_, 0, v___x_1095_);
    leanh::lean_ctor_set(v___x_1097_, 1, v___x_1096_);
    v___x_1098_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__3_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___closed__3);
    v___x_1099_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1099_, 0, v___x_1097_);
    leanh::lean_ctor_set(v___x_1099_, 1, v___x_1098_);
    v___x_1100_ = l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg(v___x_1099_, v___y_1092_, v___y_1093_);
    return v___x_1100_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg___boxed(
    mut v_optionName_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
    mut v___y_1103_: *mut leanh::LeanObject,
    mut v___y_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg(v_optionName_1101_, v___y_1102_, v___y_1103_);
    leanh::lean_dec(v___y_1103_);
    leanh::lean_dec_ref(v___y_1102_);
    return v_res_1105_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13_spec__15(
    mut v_msg_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lean_instInhabitedExpr;
    v___x_1108_ = lean_panic_fn_borrowed(v___x_1107_, v_msg_1106_);
    return v___x_1108_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__0;
    v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
    return v___x_1111_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__2;
    v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
    return v___x_1114_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1116_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__4;
    v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
    return v___x_1117_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__6;
    v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__16;
    v___x_1134_ = leanh::lean_unsigned_to_nat(14);
    v___x_1135_ = leanh::lean_unsigned_to_nat(22);
    v___x_1136_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__15;
    v___x_1137_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__14;
    v___x_1138_ = l_mkPanicMessageWithDecl(
        v___x_1137_,
        v___x_1136_,
        v___x_1135_,
        v___x_1134_,
        v___x_1133_,
    );
    return v___x_1138_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13(
    mut v_optionName_1139_: *mut leanh::LeanObject,
    mut v_found_1140_: *mut leanh::LeanObject,
    mut v_defVal_1141_: *mut leanh::LeanObject,
    mut v___y_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_v_1180_: u8 = 0;
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut v_v_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut v_v_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1207_: u8 = 0;
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut v_v_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1145_ =
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_1141_);
                if leanh::lean_obj_tag(v___x_1145_) == 1 {
                    v_val_1146_ = leanh::lean_ctor_get(v___x_1145_, 0);
                    leanh::lean_inc(v_val_1146_);
                    leanh::lean_dec_ref_known(v___x_1145_, 1);
                    v___x_1217_ =
                        l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_1140_);
                    if leanh::lean_obj_tag(v___x_1217_) == 0 {
                        v___x_1218_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__17_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__17);
                        v___x_1219_ = l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13_spec__15(v___x_1218_);
                        v___y_1169_ = v___x_1219_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1220_ = leanh::lean_ctor_get(v___x_1217_, 0);
                        leanh::lean_inc(v_val_1220_);
                        leanh::lean_dec_ref_known(v___x_1217_, 1);
                        v___y_1169_ = v_val_1220_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1145_);
                    leanh::lean_dec_ref(v_found_1140_);
                    v___x_1221_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg(v_optionName_1139_, v___y_1142_, v___y_1143_);
                    return v___x_1221_;
                }
            }
            1 => {
                v___x_1151_ = l_Lean_MessageData_ofFormat(v___y_1150_);
                v___x_1152_ = l_Lean_indentD(v___x_1151_);
                leanh::lean_inc_ref(v___y_1148_);
                v___x_1153_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1153_, 0, v___y_1148_);
                leanh::lean_ctor_set(v___x_1153_, 1, v___x_1152_);
                v___x_1154_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__1_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__1);
                v___x_1155_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1155_, 0, v___x_1153_);
                leanh::lean_ctor_set(v___x_1155_, 1, v___x_1154_);
                v___x_1156_ = l_Lean_MessageData_ofExpr(v___y_1149_);
                v___x_1157_ = l_Lean_indentD(v___x_1156_);
                v___x_1158_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1158_, 0, v___x_1155_);
                leanh::lean_ctor_set(v___x_1158_, 1, v___x_1157_);
                v___x_1159_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__3_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__3);
                v___x_1160_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
                leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
                v___x_1161_ = l_Lean_MessageData_ofName(v_optionName_1139_);
                v___x_1162_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1162_, 0, v___x_1160_);
                leanh::lean_ctor_set(v___x_1162_, 1, v___x_1161_);
                v___x_1163_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__5_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__5);
                v___x_1164_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1164_, 0, v___x_1162_);
                leanh::lean_ctor_set(v___x_1164_, 1, v___x_1163_);
                v___x_1165_ = l_Lean_indentExpr(v_val_1146_);
                v___x_1166_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1166_, 0, v___x_1164_);
                leanh::lean_ctor_set(v___x_1166_, 1, v___x_1165_);
                v___x_1167_ = l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg(v___x_1166_, v___y_1142_, v___y_1143_);
                return v___x_1167_;
            }
            2 => {
                v___x_1170_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__7_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__7);
                match leanh::lean_obj_tag(v_found_1140_) {
                    0 => {
                        v_v_1171_ = leanh::lean_ctor_get(v_found_1140_, 0);
                        v_isSharedCheck_1179_ =
                            (!leanh::lean_is_exclusive(v_found_1140_)) as u8;
                        if v_isSharedCheck_1179_ == 0 {
                            v___x_1173_ = v_found_1140_;
                            v_isShared_1174_ = v_isSharedCheck_1179_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_1171_);
                            leanh::lean_dec(v_found_1140_);
                            v___x_1173_ = leanh::lean_box(0);
                            v_isShared_1174_ = v_isSharedCheck_1179_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_v_1180_ = leanh::lean_ctor_get_uint8(v_found_1140_, 0 as u32);
                        leanh::lean_dec_ref_known(v_found_1140_, 0);
                        if v_v_1180_ == 0 {
                            v___x_1181_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__9;
                            v___y_1148_ = v___x_1170_;
                            v___y_1149_ = v___y_1169_;
                            v___y_1150_ = v___x_1181_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1182_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__11;
                            v___y_1148_ = v___x_1170_;
                            v___y_1149_ = v___y_1169_;
                            v___y_1150_ = v___x_1182_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_v_1183_ = leanh::lean_ctor_get(v_found_1140_, 0);
                        v_isSharedCheck_1194_ =
                            (!leanh::lean_is_exclusive(v_found_1140_)) as u8;
                        if v_isSharedCheck_1194_ == 0 {
                            v___x_1185_ = v_found_1140_;
                            v_isShared_1186_ = v_isSharedCheck_1194_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_1183_);
                            leanh::lean_dec(v_found_1140_);
                            v___x_1185_ = leanh::lean_box(0);
                            v_isShared_1186_ = v_isSharedCheck_1194_;
                            state = 5;
                            continue;
                        }
                    }
                    3 => {
                        v_v_1195_ = leanh::lean_ctor_get(v_found_1140_, 0);
                        v_isSharedCheck_1203_ =
                            (!leanh::lean_is_exclusive(v_found_1140_)) as u8;
                        if v_isSharedCheck_1203_ == 0 {
                            v___x_1197_ = v_found_1140_;
                            v_isShared_1198_ = v_isSharedCheck_1203_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_1195_);
                            leanh::lean_dec(v_found_1140_);
                            v___x_1197_ = leanh::lean_box(0);
                            v_isShared_1198_ = v_isSharedCheck_1203_;
                            state = 7;
                            continue;
                        }
                    }
                    4 => {
                        v_v_1204_ = leanh::lean_ctor_get(v_found_1140_, 0);
                        v_isSharedCheck_1212_ =
                            (!leanh::lean_is_exclusive(v_found_1140_)) as u8;
                        if v_isSharedCheck_1212_ == 0 {
                            v___x_1206_ = v_found_1140_;
                            v_isShared_1207_ = v_isSharedCheck_1212_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_1204_);
                            leanh::lean_dec(v_found_1140_);
                            v___x_1206_ = leanh::lean_box(0);
                            v_isShared_1207_ = v_isSharedCheck_1212_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_v_1213_ = leanh::lean_ctor_get(v_found_1140_, 0);
                        leanh::lean_inc(v_v_1213_);
                        leanh::lean_dec_ref_known(v_found_1140_, 1);
                        v___x_1214_ = leanh::lean_box(0);
                        v___x_1215_ = 0;
                        v___x_1216_ = l_Lean_Syntax_formatStx(v_v_1213_, v___x_1214_, v___x_1215_);
                        v___y_1148_ = v___x_1170_;
                        v___y_1149_ = v___y_1169_;
                        v___y_1150_ = v___x_1216_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1175_ = l_String_quote(v_v_1171_);
                if v_isShared_1174_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1173_, 3);
                    leanh::lean_ctor_set(v___x_1173_, 0, v___x_1175_);
                    v___x_1177_ = v___x_1173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
                    v___x_1177_ = v_reuseFailAlloc_1178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1148_ = v___x_1170_;
                v___y_1149_ = v___y_1169_;
                v___y_1150_ = v___x_1177_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1187_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__13;
                v___x_1188_ = 1;
                v___x_1189_ = l_Lean_Name_toString(v_v_1183_, v___x_1188_);
                if v_isShared_1186_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1185_, 3);
                    leanh::lean_ctor_set(v___x_1185_, 0, v___x_1189_);
                    v___x_1191_ = v___x_1185_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1189_);
                    v___x_1191_ = v_reuseFailAlloc_1193_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1192_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1192_, 0, v___x_1187_);
                leanh::lean_ctor_set(v___x_1192_, 1, v___x_1191_);
                v___y_1148_ = v___x_1170_;
                v___y_1149_ = v___y_1169_;
                v___y_1150_ = v___x_1192_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1199_ = l_Nat_reprFast(v_v_1195_);
                if v_isShared_1198_ == 0 {
                    leanh::lean_ctor_set(v___x_1197_, 0, v___x_1199_);
                    v___x_1201_ = v___x_1197_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
                    v___x_1201_ = v_reuseFailAlloc_1202_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_1148_ = v___x_1170_;
                v___y_1149_ = v___y_1169_;
                v___y_1150_ = v___x_1201_;
                state = 1;
                continue;
            }
            9 => {
                v___x_1208_ = l_Int_repr(v_v_1204_);
                leanh::lean_dec(v_v_1204_);
                if v_isShared_1207_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1206_, 3);
                    leanh::lean_ctor_set(v___x_1206_, 0, v___x_1208_);
                    v___x_1210_ = v___x_1206_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1211_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
                    v___x_1210_ = v_reuseFailAlloc_1211_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1148_ = v___x_1170_;
                v___y_1149_ = v___y_1169_;
                v___y_1150_ = v___x_1210_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___boxed(
    mut v_optionName_1222_: *mut leanh::LeanObject,
    mut v_found_1223_: *mut leanh::LeanObject,
    mut v_defVal_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1228_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13(v_optionName_1222_, v_found_1223_, v_defVal_1224_, v___y_1225_, v___y_1226_);
    leanh::lean_dec(v___y_1226_);
    leanh::lean_dec_ref(v___y_1225_);
    leanh::lean_dec_ref(v_defVal_1224_);
    return v_res_1228_;
}
pub unsafe fn l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8(
    mut v_optionName_1229_: *mut leanh::LeanObject,
    mut v_decl_1230_: *mut leanh::LeanObject,
    mut v_val_1231_: *mut leanh::LeanObject,
    mut v___y_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    v_defValue_1235_ = leanh::lean_ctor_get(v_decl_1230_, 2);
    v___x_1236_ = l_Lean_DataValue_sameCtor(v_defValue_1235_, v_val_1231_);
    if v___x_1236_ == 0 {
        let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1237_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13(v_optionName_1229_, v_val_1231_, v_defValue_1235_, v___y_1232_, v___y_1233_);
        return v___x_1237_;
    } else {
        let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_val_1231_);
        leanh::lean_dec(v_optionName_1229_);
        v___x_1238_ = leanh::lean_box(0);
        v___x_1239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
        return v___x_1239_;
    }
}
pub unsafe fn l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8___boxed(
    mut v_optionName_1240_: *mut leanh::LeanObject,
    mut v_decl_1241_: *mut leanh::LeanObject,
    mut v_val_1242_: *mut leanh::LeanObject,
    mut v___y_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8(v_optionName_1240_, v_decl_1241_, v_val_1242_, v___y_1243_, v___y_1244_);
    leanh::lean_dec(v___y_1244_);
    leanh::lean_dec_ref(v___y_1243_);
    leanh::lean_dec_ref(v_decl_1241_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9(
    mut v_o_1250_: *mut leanh::LeanObject,
    mut v_k_1251_: *mut leanh::LeanObject,
    mut v_v_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1254_: u8 = 0;
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1253_ = leanh::lean_ctor_get(v_o_1250_, 0);
                v_hasTrace_1254_ = leanh::lean_ctor_get_uint8(
                    v_o_1250_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1267_ = (!leanh::lean_is_exclusive(v_o_1250_)) as u8;
                if v_isSharedCheck_1267_ == 0 {
                    v___x_1256_ = v_o_1250_;
                    v_isShared_1257_ = v_isSharedCheck_1267_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_1253_);
                    leanh::lean_dec(v_o_1250_);
                    v___x_1256_ = leanh::lean_box(0);
                    v_isShared_1257_ = v_isSharedCheck_1267_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_k_1251_);
                v___x_1258_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1251_, v_v_1252_, v_map_1253_);
                if v_hasTrace_1254_ == 0 {
                    v___x_1259_ = l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9___closed__1;
                    v___x_1260_ = l_Lean_Name_isPrefixOf(v___x_1259_, v_k_1251_);
                    leanh::lean_dec(v_k_1251_);
                    if v_isShared_1257_ == 0 {
                        leanh::lean_ctor_set(v___x_1256_, 0, v___x_1258_);
                        v___x_1262_ = v___x_1256_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1263_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1258_);
                        v___x_1262_ = v_reuseFailAlloc_1263_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1251_);
                    if v_isShared_1257_ == 0 {
                        leanh::lean_ctor_set(v___x_1256_, 0, v___x_1258_);
                        v___x_1265_ = v___x_1256_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1266_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1258_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1266_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1254_,
                        );
                        v___x_1265_ = v_reuseFailAlloc_1266_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1262_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1260_,
                );
                return v___x_1262_;
            }
            3 => {
                return v___x_1265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4(
    mut v_optionName_1268_: *mut leanh::LeanObject,
    mut v_decl_1269_: *mut leanh::LeanObject,
    mut v_val_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut v_unused_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1293_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_val_1270_);
                leanh::lean_inc(v_optionName_1268_);
                v___x_1274_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8(v_optionName_1268_, v_decl_1269_, v_val_1270_, v___y_1271_, v___y_1272_);
                if leanh::lean_obj_tag(v___x_1274_) == 0 {
                    v_isSharedCheck_1288_ = (!leanh::lean_is_exclusive(v___x_1274_)) as u8;
                    if v_isSharedCheck_1288_ == 0 {
                        v_unused_1289_ = leanh::lean_ctor_get(v___x_1274_, 0);
                        leanh::lean_dec(v_unused_1289_);
                        v___x_1276_ = v___x_1274_;
                        v_isShared_1277_ = v_isSharedCheck_1288_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1274_);
                        v___x_1276_ = leanh::lean_box(0);
                        v_isShared_1277_ = v_isSharedCheck_1288_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_val_1270_);
                    leanh::lean_dec_ref(v_decl_1269_);
                    leanh::lean_dec(v_optionName_1268_);
                    v_a_1290_ = leanh::lean_ctor_get(v___x_1274_, 0);
                    v_isSharedCheck_1297_ = (!leanh::lean_is_exclusive(v___x_1274_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v___x_1292_ = v___x_1274_;
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1290_);
                        leanh::lean_dec(v___x_1274_);
                        v___x_1292_ = leanh::lean_box(0);
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1278_ = lean_st_ref_get(v___y_1272_);
                v_scopes_1279_ = leanh::lean_ctor_get(v___x_1278_, 2);
                leanh::lean_inc(v_scopes_1279_);
                leanh::lean_dec(v___x_1278_);
                v___x_1280_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1281_ = l_List_head_x21___redArg(v___x_1280_, v_scopes_1279_);
                leanh::lean_dec(v_scopes_1279_);
                v_opts_1282_ = leanh::lean_ctor_get(v___x_1281_, 1);
                leanh::lean_inc_ref(v_opts_1282_);
                leanh::lean_dec(v___x_1281_);
                v___x_1283_ = l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__9(v_opts_1282_, v_optionName_1268_, v_val_1270_);
                v___x_1284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
                leanh::lean_ctor_set(v___x_1284_, 1, v_decl_1269_);
                if v_isShared_1277_ == 0 {
                    leanh::lean_ctor_set(v___x_1276_, 0, v___x_1284_);
                    v___x_1286_ = v___x_1276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
                    v___x_1286_ = v_reuseFailAlloc_1287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1286_;
            }
            3 => {
                if v_isShared_1293_ == 0 {
                    v___x_1295_ = v___x_1292_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4___boxed(
    mut v_optionName_1298_: *mut leanh::LeanObject,
    mut v_decl_1299_: *mut leanh::LeanObject,
    mut v_val_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4(v_optionName_1298_, v_decl_1299_, v_val_1300_, v___y_1301_, v___y_1302_);
    leanh::lean_dec(v___y_1302_);
    leanh::lean_dec_ref(v___y_1301_);
    return v_res_1304_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__0(
    mut v_info_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1309_ = leanh::lean_alloc_ctor(8, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1309_, 0, v_info_1305_);
    v___x_1310_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1(v___x_1309_, v___y_1306_, v___y_1307_);
    return v___x_1310_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__0___boxed(
    mut v_info_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
    mut v___y_1313_: *mut leanh::LeanObject,
    mut v___y_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__0(v_info_1311_, v___y_1312_, v___y_1313_);
    leanh::lean_dec(v___y_1313_);
    leanh::lean_dec_ref(v___y_1312_);
    return v_res_1315_;
}
pub unsafe fn _init_l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__0;
    v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn _init_l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__2;
    v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
    return v___x_1321_;
}
pub unsafe fn _init_l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__12;
    v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
    return v___x_1323_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0(
    mut v_id_1324_: *mut leanh::LeanObject,
    mut v_val_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionName_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1385_: u8 = 0;
    let mut v_val_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_reuseFailAlloc_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1399_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1409_: u8 = 0;
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_unused_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1329_ = l_Lean_Elab_Command_getRef___redArg(v___y_1326_);
                if leanh::lean_obj_tag(v___x_1329_) == 0 {
                    v_a_1330_ = leanh::lean_ctor_get(v___x_1329_, 0);
                    leanh::lean_inc_n(v_a_1330_, 2);
                    leanh::lean_dec_ref_known(v___x_1329_, 1);
                    v___x_1331_ = l_Lean_Syntax_getArgs(v_a_1330_);
                    v___x_1332_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1333_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1334_ =
                        l_Array_toSubarray___redArg(v___x_1331_, v___x_1333_, v___x_1332_);
                    v___x_1335_ = l_Subarray_copy___redArg(v___x_1334_);
                    v___x_1336_ = l_Lean_Syntax_setArgs(v_a_1330_, v___x_1335_);
                    v___x_1337_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1337_, 0, v___x_1336_);
                    v___x_1338_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__0(v___x_1337_, v___y_1326_, v___y_1327_);
                    v_isSharedCheck_1410_ = (!leanh::lean_is_exclusive(v___x_1338_)) as u8;
                    if v_isSharedCheck_1410_ == 0 {
                        v_unused_1411_ = leanh::lean_ctor_get(v___x_1338_, 0);
                        leanh::lean_dec(v_unused_1411_);
                        v___x_1340_ = v___x_1338_;
                        v_isShared_1341_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1338_);
                        v___x_1340_ = leanh::lean_box(0);
                        v_isShared_1341_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_val_1325_);
                    leanh::lean_dec(v_id_1324_);
                    v_a_1412_ = leanh::lean_ctor_get(v___x_1329_, 0);
                    v_isSharedCheck_1419_ = (!leanh::lean_is_exclusive(v___x_1329_)) as u8;
                    if v_isSharedCheck_1419_ == 0 {
                        v___x_1414_ = v___x_1329_;
                        v_isShared_1415_ = v_isSharedCheck_1419_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1412_);
                        leanh::lean_dec(v___x_1329_);
                        v___x_1414_ = leanh::lean_box(0);
                        v_isShared_1415_ = v_isSharedCheck_1419_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1342_ = l_Lean_Syntax_getId(v_id_1324_);
                v_optionName_1343_ = lean_erase_macro_scopes(v___x_1342_);
                leanh::lean_inc(v_optionName_1343_);
                v___x_1344_ = l_Lean_getOptionDecl(v_optionName_1343_);
                if leanh::lean_obj_tag(v___x_1344_) == 0 {
                    leanh::lean_dec(v_a_1330_);
                    v_a_1345_ = leanh::lean_ctor_get(v___x_1344_, 0);
                    leanh::lean_inc(v_a_1345_);
                    leanh::lean_dec_ref_known(v___x_1344_, 1);
                    v_declName_1346_ = leanh::lean_ctor_get(v_a_1345_, 1);
                    v_defValue_1347_ = leanh::lean_ctor_get(v_a_1345_, 2);
                    leanh::lean_inc(v_declName_1346_);
                    leanh::lean_inc(v_optionName_1343_);
                    v___x_1348_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1348_, 0, v_id_1324_);
                    leanh::lean_ctor_set(v___x_1348_, 1, v_optionName_1343_);
                    leanh::lean_ctor_set(v___x_1348_, 2, v_declName_1346_);
                    if v_isShared_1341_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1340_, 5);
                        leanh::lean_ctor_set(v___x_1340_, 0, v___x_1348_);
                        v___x_1350_ = v___x_1340_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1395_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1348_);
                        v___x_1350_ = v_reuseFailAlloc_1395_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_optionName_1343_);
                    leanh::lean_dec(v_val_1325_);
                    leanh::lean_dec(v_id_1324_);
                    v_a_1396_ = leanh::lean_ctor_get(v___x_1344_, 0);
                    v_isSharedCheck_1409_ = (!leanh::lean_is_exclusive(v___x_1344_)) as u8;
                    if v_isSharedCheck_1409_ == 0 {
                        v___x_1398_ = v___x_1344_;
                        v_isShared_1399_ = v_isSharedCheck_1409_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1396_);
                        leanh::lean_dec(v___x_1344_);
                        v___x_1398_ = leanh::lean_box(0);
                        v_isShared_1399_ = v_isSharedCheck_1409_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1351_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1(v___x_1350_, v___y_1326_, v___y_1327_);
                leanh::lean_dec_ref(v___x_1351_);
                v___x_1366_ = l_Lean_Syntax_isStrLit_x3f(v_val_1325_);
                if leanh::lean_obj_tag(v___x_1366_) == 0 {
                    v___x_1367_ = l_Lean_Syntax_isNatLit_x3f(v_val_1325_);
                    if leanh::lean_obj_tag(v___x_1367_) == 0 {
                        if leanh::lean_obj_tag(v_val_1325_) == 2 {
                            v_val_1368_ = leanh::lean_ctor_get(v_val_1325_, 1);
                            v___x_1369_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__10;
                            v___x_1370_ = lean_string_dec_eq(v_val_1368_, v___x_1369_);
                            if v___x_1370_ == 0 {
                                v___x_1371_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4_spec__8_spec__13___closed__8;
                                v___x_1372_ = lean_string_dec_eq(v_val_1368_, v___x_1371_);
                                if v___x_1372_ == 0 {
                                    leanh::lean_inc_ref(v_defValue_1347_);
                                    leanh::lean_dec(v_a_1345_);
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref_known(v_val_1325_, 2);
                                    v___x_1373_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1373_,
                                        0 as u32,
                                        v___x_1370_,
                                    );
                                    v___x_1374_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4(v_optionName_1343_, v_a_1345_, v___x_1373_, v___y_1326_, v___y_1327_);
                                    return v___x_1374_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_val_1325_, 2);
                                v___x_1375_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                                leanh::lean_ctor_set_uint8(
                                    v___x_1375_,
                                    0 as u32,
                                    v___x_1370_,
                                );
                                v___x_1376_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4(v_optionName_1343_, v_a_1345_, v___x_1375_, v___y_1326_, v___y_1327_);
                                return v___x_1376_;
                            }
                        } else {
                            leanh::lean_inc_ref(v_defValue_1347_);
                            leanh::lean_dec(v_a_1345_);
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_1325_);
                        v_val_1377_ = leanh::lean_ctor_get(v___x_1367_, 0);
                        v_isSharedCheck_1385_ =
                            (!leanh::lean_is_exclusive(v___x_1367_)) as u8;
                        if v_isSharedCheck_1385_ == 0 {
                            v___x_1379_ = v___x_1367_;
                            v_isShared_1380_ = v_isSharedCheck_1385_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1377_);
                            leanh::lean_dec(v___x_1367_);
                            v___x_1379_ = leanh::lean_box(0);
                            v_isShared_1380_ = v_isSharedCheck_1385_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_1325_);
                    v_val_1386_ = leanh::lean_ctor_get(v___x_1366_, 0);
                    v_isSharedCheck_1394_ = (!leanh::lean_is_exclusive(v___x_1366_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v___x_1388_ = v___x_1366_;
                        v_isShared_1389_ = v_isSharedCheck_1394_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1386_);
                        leanh::lean_dec(v___x_1366_);
                        v___x_1388_ = leanh::lean_box(0);
                        v_isShared_1389_ = v_isSharedCheck_1394_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1353_ =
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_1347_);
                leanh::lean_dec_ref(v_defValue_1347_);
                if leanh::lean_obj_tag(v___x_1353_) == 1 {
                    leanh::lean_dec(v_optionName_1343_);
                    v_val_1354_ = leanh::lean_ctor_get(v___x_1353_, 0);
                    leanh::lean_inc(v_val_1354_);
                    leanh::lean_dec_ref_known(v___x_1353_, 1);
                    v___x_1355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__1_once), _init_l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__1);
                    v___x_1356_ = l_Lean_MessageData_ofSyntax(v_val_1325_);
                    v___x_1357_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1357_, 0, v___x_1355_);
                    leanh::lean_ctor_set(v___x_1357_, 1, v___x_1356_);
                    v___x_1358_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__3_once), _init_l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__3);
                    v___x_1359_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1359_, 0, v___x_1357_);
                    leanh::lean_ctor_set(v___x_1359_, 1, v___x_1358_);
                    v___x_1360_ = l_Lean_MessageData_ofExpr(v_val_1354_);
                    v___x_1361_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1361_, 0, v___x_1359_);
                    leanh::lean_ctor_set(v___x_1361_, 1, v___x_1360_);
                    v___x_1362_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__4_once), _init_l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___closed__4);
                    v___x_1363_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1363_, 0, v___x_1361_);
                    leanh::lean_ctor_set(v___x_1363_, 1, v___x_1362_);
                    v___x_1364_ = l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg(v___x_1363_, v___y_1326_, v___y_1327_);
                    return v___x_1364_;
                } else {
                    leanh::lean_dec(v___x_1353_);
                    leanh::lean_dec(v_val_1325_);
                    v___x_1365_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg(v_optionName_1343_, v___y_1326_, v___y_1327_);
                    return v___x_1365_;
                }
            }
            4 => {
                if v_isShared_1380_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1379_, 3);
                    v___x_1382_ = v___x_1379_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1384_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_val_1377_);
                    v___x_1382_ = v_reuseFailAlloc_1384_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1383_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4(v_optionName_1343_, v_a_1345_, v___x_1382_, v___y_1326_, v___y_1327_);
                return v___x_1383_;
            }
            6 => {
                if v_isShared_1389_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1388_, 0);
                    v___x_1391_ = v___x_1388_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1386_);
                    v___x_1391_ = v_reuseFailAlloc_1393_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1392_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__4(v_optionName_1343_, v_a_1345_, v___x_1391_, v___y_1326_, v___y_1327_);
                return v___x_1392_;
            }
            8 => {
                v___x_1400_ = lean_io_error_to_string(v_a_1396_);
                if v_isShared_1341_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1340_, 3);
                    leanh::lean_ctor_set(v___x_1340_, 0, v___x_1400_);
                    v___x_1402_ = v___x_1340_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1400_);
                    v___x_1402_ = v_reuseFailAlloc_1408_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1403_ = l_Lean_MessageData_ofFormat(v___x_1402_);
                v___x_1404_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1404_, 0, v_a_1330_);
                leanh::lean_ctor_set(v___x_1404_, 1, v___x_1403_);
                if v_isShared_1399_ == 0 {
                    leanh::lean_ctor_set(v___x_1398_, 0, v___x_1404_);
                    v___x_1406_ = v___x_1398_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
                    v___x_1406_ = v_reuseFailAlloc_1407_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1406_;
            }
            11 => {
                if v_isShared_1415_ == 0 {
                    v___x_1417_ = v___x_1414_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
                    v___x_1417_ = v_reuseFailAlloc_1418_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0___boxed(
    mut v_id_1420_: *mut leanh::LeanObject,
    mut v_val_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0(
        v_id_1420_,
        v_val_1421_,
        v___y_1422_,
        v___y_1423_,
    );
    leanh::lean_dec(v___y_1423_);
    leanh::lean_dec_ref(v___y_1422_);
    return v_res_1425_;
}
pub unsafe fn l_Lean_withSetOptionIn___lam__0(
    mut v___x_1426_: *mut leanh::LeanObject,
    mut v___x_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v_fst_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut v_a_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1431_ = l_Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0(
                    v___x_1426_,
                    v___x_1427_,
                    v___y_1428_,
                    v___y_1429_,
                );
                if leanh::lean_obj_tag(v___x_1431_) == 0 {
                    v_a_1432_ = leanh::lean_ctor_get(v___x_1431_, 0);
                    v_isSharedCheck_1440_ = (!leanh::lean_is_exclusive(v___x_1431_)) as u8;
                    if v_isSharedCheck_1440_ == 0 {
                        v___x_1434_ = v___x_1431_;
                        v_isShared_1435_ = v_isSharedCheck_1440_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1432_);
                        leanh::lean_dec(v___x_1431_);
                        v___x_1434_ = leanh::lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1440_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1441_ = leanh::lean_ctor_get(v___x_1431_, 0);
                    v_isSharedCheck_1457_ = (!leanh::lean_is_exclusive(v___x_1431_)) as u8;
                    if v_isSharedCheck_1457_ == 0 {
                        v___x_1443_ = v___x_1431_;
                        v_isShared_1444_ = v_isSharedCheck_1457_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1441_);
                        leanh::lean_dec(v___x_1431_);
                        v___x_1443_ = leanh::lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1457_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1436_ = leanh::lean_ctor_get(v_a_1432_, 0);
                leanh::lean_inc(v_fst_1436_);
                leanh::lean_dec(v_a_1432_);
                if v_isShared_1435_ == 0 {
                    leanh::lean_ctor_set(v___x_1434_, 0, v_fst_1436_);
                    v___x_1438_ = v___x_1434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_fst_1436_);
                    v___x_1438_ = v_reuseFailAlloc_1439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1438_;
            }
            3 => {
                v___x_1445_ = l_Lean_Exception_isInterrupt(v_a_1441_);
                if v___x_1445_ == 0 {
                    leanh::lean_dec(v_a_1441_);
                    v___x_1446_ = lean_st_ref_get(v___y_1429_);
                    v_scopes_1447_ = leanh::lean_ctor_get(v___x_1446_, 2);
                    leanh::lean_inc(v_scopes_1447_);
                    leanh::lean_dec(v___x_1446_);
                    v___x_1448_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1449_ = l_List_head_x21___redArg(v___x_1448_, v_scopes_1447_);
                    leanh::lean_dec(v_scopes_1447_);
                    v_opts_1450_ = leanh::lean_ctor_get(v___x_1449_, 1);
                    leanh::lean_inc_ref(v_opts_1450_);
                    leanh::lean_dec(v___x_1449_);
                    if v_isShared_1444_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1443_, 0);
                        leanh::lean_ctor_set(v___x_1443_, 0, v_opts_1450_);
                        v___x_1452_ = v___x_1443_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_opts_1450_);
                        v___x_1452_ = v_reuseFailAlloc_1453_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_1444_ == 0 {
                        v___x_1455_ = v___x_1443_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1441_);
                        v___x_1455_ = v_reuseFailAlloc_1456_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1452_;
            }
            5 => {
                return v___x_1455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withSetOptionIn___lam__0___boxed(
    mut v___x_1458_: *mut leanh::LeanObject,
    mut v___x_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ =
        l_Lean_withSetOptionIn___lam__0(v___x_1458_, v___x_1459_, v___y_1460_, v___y_1461_);
    leanh::lean_dec(v___y_1461_);
    leanh::lean_dec_ref(v___y_1460_);
    return v_res_1463_;
}
pub unsafe fn l_Lean_withSetOptionIn___lam__1(
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_x_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_header_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varDecls_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varUIds_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includedVars_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_1474_: u8 = 0;
    let mut v_isPublic_1475_: u8 = 0;
    let mut v_isMeta_1476_: u8 = 0;
    let mut v_attrs_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut v_unused_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_1466_ = leanh::lean_ctor_get(v_x_1465_, 0);
                v_currNamespace_1467_ = leanh::lean_ctor_get(v_x_1465_, 2);
                v_openDecls_1468_ = leanh::lean_ctor_get(v_x_1465_, 3);
                v_levelNames_1469_ = leanh::lean_ctor_get(v_x_1465_, 4);
                v_varDecls_1470_ = leanh::lean_ctor_get(v_x_1465_, 5);
                v_varUIds_1471_ = leanh::lean_ctor_get(v_x_1465_, 6);
                v_includedVars_1472_ = leanh::lean_ctor_get(v_x_1465_, 7);
                v_omittedVars_1473_ = leanh::lean_ctor_get(v_x_1465_, 8);
                v_isNoncomputable_1474_ = leanh::lean_ctor_get_uint8(
                    v_x_1465_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v_isPublic_1475_ = leanh::lean_ctor_get_uint8(
                    v_x_1465_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_1476_ = leanh::lean_ctor_get_uint8(
                    v_x_1465_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_1477_ = leanh::lean_ctor_get(v_x_1465_, 9);
                v_isSharedCheck_1484_ = (!leanh::lean_is_exclusive(v_x_1465_)) as u8;
                if v_isSharedCheck_1484_ == 0 {
                    v_unused_1485_ = leanh::lean_ctor_get(v_x_1465_, 1);
                    leanh::lean_dec(v_unused_1485_);
                    v___x_1479_ = v_x_1465_;
                    v_isShared_1480_ = v_isSharedCheck_1484_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_attrs_1477_);
                    leanh::lean_inc(v_omittedVars_1473_);
                    leanh::lean_inc(v_includedVars_1472_);
                    leanh::lean_inc(v_varUIds_1471_);
                    leanh::lean_inc(v_varDecls_1470_);
                    leanh::lean_inc(v_levelNames_1469_);
                    leanh::lean_inc(v_openDecls_1468_);
                    leanh::lean_inc(v_currNamespace_1467_);
                    leanh::lean_inc(v_header_1466_);
                    leanh::lean_dec(v_x_1465_);
                    v___x_1479_ = leanh::lean_box(0);
                    v_isShared_1480_ = v_isSharedCheck_1484_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1480_ == 0 {
                    leanh::lean_ctor_set(v___x_1479_, 1, v_a_1464_);
                    v___x_1482_ = v___x_1479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = leanh::lean_alloc_ctor(0, 10, (3) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_header_1466_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_currNamespace_1467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_openDecls_1468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_levelNames_1469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 5, v_varDecls_1470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 6, v_varUIds_1471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 7, v_includedVars_1472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 8, v_omittedVars_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 9, v_attrs_1477_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1483_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_isNoncomputable_1474_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1483_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1) as u32,
                        v_isPublic_1475_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1483_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2) as u32,
                        v_isMeta_1476_,
                    );
                    v___x_1482_ = v_reuseFailAlloc_1483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg(
    mut v_flag_1486_: u8,
    mut v___y_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v_assignment_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1519_: u8 = 0;
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1489_ = lean_st_ref_take(v___y_1487_);
                v_infoState_1490_ = leanh::lean_ctor_get(v___x_1489_, 8);
                v_env_1491_ = leanh::lean_ctor_get(v___x_1489_, 0);
                v_messages_1492_ = leanh::lean_ctor_get(v___x_1489_, 1);
                v_scopes_1493_ = leanh::lean_ctor_get(v___x_1489_, 2);
                v_usedQuotCtxts_1494_ = leanh::lean_ctor_get(v___x_1489_, 3);
                v_nextMacroScope_1495_ = leanh::lean_ctor_get(v___x_1489_, 4);
                v_maxRecDepth_1496_ = leanh::lean_ctor_get(v___x_1489_, 5);
                v_ngen_1497_ = leanh::lean_ctor_get(v___x_1489_, 6);
                v_auxDeclNGen_1498_ = leanh::lean_ctor_get(v___x_1489_, 7);
                v_traceState_1499_ = leanh::lean_ctor_get(v___x_1489_, 9);
                v_snapshotTasks_1500_ = leanh::lean_ctor_get(v___x_1489_, 10);
                v_isSharedCheck_1520_ = (!leanh::lean_is_exclusive(v___x_1489_)) as u8;
                if v_isSharedCheck_1520_ == 0 {
                    v___x_1502_ = v___x_1489_;
                    v_isShared_1503_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1500_);
                    leanh::lean_inc(v_traceState_1499_);
                    leanh::lean_inc(v_infoState_1490_);
                    leanh::lean_inc(v_auxDeclNGen_1498_);
                    leanh::lean_inc(v_ngen_1497_);
                    leanh::lean_inc(v_maxRecDepth_1496_);
                    leanh::lean_inc(v_nextMacroScope_1495_);
                    leanh::lean_inc(v_usedQuotCtxts_1494_);
                    leanh::lean_inc(v_scopes_1493_);
                    leanh::lean_inc(v_messages_1492_);
                    leanh::lean_inc(v_env_1491_);
                    leanh::lean_dec(v___x_1489_);
                    v___x_1502_ = leanh::lean_box(0);
                    v_isShared_1503_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_assignment_1504_ = leanh::lean_ctor_get(v_infoState_1490_, 0);
                v_lazyAssignment_1505_ = leanh::lean_ctor_get(v_infoState_1490_, 1);
                v_trees_1506_ = leanh::lean_ctor_get(v_infoState_1490_, 2);
                v_isSharedCheck_1519_ = (!leanh::lean_is_exclusive(v_infoState_1490_)) as u8;
                if v_isSharedCheck_1519_ == 0 {
                    v___x_1508_ = v_infoState_1490_;
                    v_isShared_1509_ = v_isSharedCheck_1519_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_trees_1506_);
                    leanh::lean_inc(v_lazyAssignment_1505_);
                    leanh::lean_inc(v_assignment_1504_);
                    leanh::lean_dec(v_infoState_1490_);
                    v___x_1508_ = leanh::lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1509_ == 0 {
                    v___x_1511_ = v___x_1508_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1518_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_assignment_1504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_lazyAssignment_1505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_trees_1506_);
                    v___x_1511_ = v_reuseFailAlloc_1518_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1511_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_flag_1486_,
                );
                if v_isShared_1503_ == 0 {
                    leanh::lean_ctor_set(v___x_1502_, 8, v___x_1511_);
                    v___x_1513_ = v___x_1502_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_env_1491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_messages_1492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_scopes_1493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_usedQuotCtxts_1494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_nextMacroScope_1495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 5, v_maxRecDepth_1496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 6, v_ngen_1497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 7, v_auxDeclNGen_1498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 8, v___x_1511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 9, v_traceState_1499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 10, v_snapshotTasks_1500_);
                    v___x_1513_ = v_reuseFailAlloc_1517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1514_ = lean_st_ref_set(v___y_1487_, v___x_1513_);
                v___x_1515_ = leanh::lean_box(0);
                v___x_1516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1516_, 0, v___x_1515_);
                return v___x_1516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg___boxed(
    mut v_flag_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_1524_: u8 = 0;
    let mut v_res_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_1524_ = (leanh::lean_unbox(v_flag_1521_) as u8);
    v_res_1525_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg(v_flag_boxed_1524_, v___y_1522_);
    leanh::lean_dec(v___y_1522_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1___redArg(
    mut v_flag_1526_: u8,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_1533_: u8 = 0;
    let mut v_a_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v_unused_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1555_: u8 = 0;
    let mut v_unused_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1531_ = lean_st_ref_get(v___y_1529_);
                v_infoState_1532_ = leanh::lean_ctor_get(v___x_1531_, 8);
                leanh::lean_inc_ref(v_infoState_1532_);
                leanh::lean_dec(v___x_1531_);
                v_enabled_1533_ = leanh::lean_ctor_get_uint8(
                    v_infoState_1532_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_1532_);
                v___x_1545_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg(v_flag_1526_, v___y_1529_);
                leanh::lean_dec_ref(v___x_1545_);
                leanh::lean_inc(v___y_1529_);
                leanh::lean_inc_ref(v___y_1528_);
                v___x_1546_ = leanh::lean_apply_3(
                    v_x_1527_,
                    v___y_1528_,
                    v___y_1529_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1546_) == 0 {
                    v_a_1547_ = leanh::lean_ctor_get(v___x_1546_, 0);
                    leanh::lean_inc(v_a_1547_);
                    leanh::lean_dec_ref_known(v___x_1546_, 1);
                    v___x_1548_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg(v_enabled_1533_, v___y_1529_);
                    v_isSharedCheck_1555_ = (!leanh::lean_is_exclusive(v___x_1548_)) as u8;
                    if v_isSharedCheck_1555_ == 0 {
                        v_unused_1556_ = leanh::lean_ctor_get(v___x_1548_, 0);
                        leanh::lean_dec(v_unused_1556_);
                        v___x_1550_ = v___x_1548_;
                        v_isShared_1551_ = v_isSharedCheck_1555_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1548_);
                        v___x_1550_ = leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1555_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1557_ = leanh::lean_ctor_get(v___x_1546_, 0);
                    leanh::lean_inc(v_a_1557_);
                    leanh::lean_dec_ref_known(v___x_1546_, 1);
                    v_a_1535_ = v_a_1557_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1536_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg(v_enabled_1533_, v___y_1529_);
                v_isSharedCheck_1543_ = (!leanh::lean_is_exclusive(v___x_1536_)) as u8;
                if v_isSharedCheck_1543_ == 0 {
                    v_unused_1544_ = leanh::lean_ctor_get(v___x_1536_, 0);
                    leanh::lean_dec(v_unused_1544_);
                    v___x_1538_ = v___x_1536_;
                    v_isShared_1539_ = v_isSharedCheck_1543_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1536_);
                    v___x_1538_ = leanh::lean_box(0);
                    v_isShared_1539_ = v_isSharedCheck_1543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1539_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1538_, 1);
                    leanh::lean_ctor_set(v___x_1538_, 0, v_a_1535_);
                    v___x_1541_ = v___x_1538_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1535_);
                    v___x_1541_ = v_reuseFailAlloc_1542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1541_;
            }
            4 => {
                if v_isShared_1551_ == 0 {
                    leanh::lean_ctor_set(v___x_1550_, 0, v_a_1547_);
                    v___x_1553_ = v___x_1550_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1554_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1547_);
                    v___x_1553_ = v_reuseFailAlloc_1554_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1___redArg___boxed(
    mut v_flag_1558_: *mut leanh::LeanObject,
    mut v_x_1559_: *mut leanh::LeanObject,
    mut v___y_1560_: *mut leanh::LeanObject,
    mut v___y_1561_: *mut leanh::LeanObject,
    mut v___y_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_1563_: u8 = 0;
    let mut v_res_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_1563_ = (leanh::lean_unbox(v_flag_1558_) as u8);
    v_res_1564_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1___redArg(
        v_flag_boxed_1563_,
        v_x_1559_,
        v___y_1560_,
        v___y_1561_,
    );
    leanh::lean_dec(v___y_1561_);
    leanh::lean_dec_ref(v___y_1560_);
    return v_res_1564_;
}
pub unsafe fn l_Lean_withSetOptionIn___boxed(
    mut v_cmd_1580_: *mut leanh::LeanObject,
    mut v_stx_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
    mut v_a_1583_: *mut leanh::LeanObject,
    mut v_a_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Lean_withSetOptionIn(v_cmd_1580_, v_stx_1581_, v_a_1582_, v_a_1583_);
    leanh::lean_dec(v_a_1583_);
    leanh::lean_dec_ref(v_a_1582_);
    return v_res_1585_;
}
pub unsafe fn l_Lean_withSetOptionIn(
    mut v_cmd_1586_: *mut leanh::LeanObject,
    mut v_stx_1587_: *mut leanh::LeanObject,
    mut v_a_1588_: *mut leanh::LeanObject,
    mut v_a_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1592_: u8 = 0;
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_1587_);
                v___x_1617_ = l_Lean_Syntax_getKind(v_stx_1587_);
                v___x_1618_ = l_Lean_withSetOptionIn___closed__4;
                v___x_1619_ = lean_name_eq(v___x_1617_, v___x_1618_);
                leanh::lean_dec(v___x_1617_);
                if v___x_1619_ == 0 {
                    v___y_1592_ = v___x_1619_;
                    state = 1;
                    continue;
                } else {
                    v___x_1620_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1621_ = l_Lean_Syntax_getArg(v_stx_1587_, v___x_1620_);
                    v___x_1622_ = l_Lean_Syntax_getKind(v___x_1621_);
                    v___x_1623_ = l_Lean_withSetOptionIn___closed__6;
                    v___x_1624_ = lean_name_eq(v___x_1622_, v___x_1623_);
                    leanh::lean_dec(v___x_1622_);
                    v___y_1592_ = v___x_1624_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1592_ == 0 {
                    leanh::lean_inc(v_a_1589_);
                    leanh::lean_inc_ref(v_a_1588_);
                    v___x_1593_ = leanh::lean_apply_4(
                        v_cmd_1586_,
                        v_stx_1587_,
                        v_a_1588_,
                        v_a_1589_,
                        leanh::lean_box(0),
                    );
                    return v___x_1593_;
                } else {
                    v___x_1594_ = 0;
                    v___x_1595_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1596_ = l_Lean_Syntax_getArg(v_stx_1587_, v___x_1595_);
                    v___x_1597_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1598_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1597_);
                    v___x_1599_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1600_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1599_);
                    leanh::lean_dec(v___x_1596_);
                    v___f_1601_ = leanh::lean_alloc_closure(
                        l_Lean_withSetOptionIn___lam__0___boxed as *mut core::ffi::c_void,
                        5,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1601_, 0, v___x_1598_);
                    leanh::lean_closure_set(v___f_1601_, 1, v___x_1600_);
                    v___x_1602_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1___redArg(v___x_1594_, v___f_1601_, v_a_1588_, v_a_1589_);
                    if leanh::lean_obj_tag(v___x_1602_) == 0 {
                        v_a_1603_ = leanh::lean_ctor_get(v___x_1602_, 0);
                        leanh::lean_inc(v_a_1603_);
                        leanh::lean_dec_ref_known(v___x_1602_, 1);
                        v___f_1604_ = leanh::lean_alloc_closure(
                            l_Lean_withSetOptionIn___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_1604_, 0, v_a_1603_);
                        v___x_1605_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1606_ = l_Lean_Syntax_getArg(v_stx_1587_, v___x_1605_);
                        leanh::lean_dec(v_stx_1587_);
                        v___x_1607_ = leanh::lean_alloc_closure(
                            l_Lean_withSetOptionIn___boxed as *mut core::ffi::c_void,
                            5,
                            2,
                        );
                        leanh::lean_closure_set(v___x_1607_, 0, v_cmd_1586_);
                        leanh::lean_closure_set(v___x_1607_, 1, v___x_1606_);
                        v___x_1608_ = l_Lean_Elab_Command_withScope___redArg(
                            v___f_1604_,
                            v___x_1607_,
                            v_a_1588_,
                            v_a_1589_,
                        );
                        return v___x_1608_;
                    } else {
                        leanh::lean_dec(v_stx_1587_);
                        leanh::lean_dec_ref(v_cmd_1586_);
                        v_a_1609_ = leanh::lean_ctor_get(v___x_1602_, 0);
                        v_isSharedCheck_1616_ =
                            (!leanh::lean_is_exclusive(v___x_1602_)) as u8;
                        if v_isSharedCheck_1616_ == 0 {
                            v___x_1611_ = v___x_1602_;
                            v_isShared_1612_ = v_isSharedCheck_1616_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1609_);
                            leanh::lean_dec(v___x_1602_);
                            v___x_1611_ = leanh::lean_box(0);
                            v_isShared_1612_ = v_isSharedCheck_1616_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_1612_ == 0 {
                    v___x_1614_ = v___x_1611_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
                    v___x_1614_ = v_reuseFailAlloc_1615_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6(
    mut v_flag_1625_: u8,
    mut v___y_1626_: *mut leanh::LeanObject,
    mut v___y_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___redArg(v_flag_1625_, v___y_1627_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6___boxed(
    mut v_flag_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
    mut v___y_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_1634_: u8 = 0;
    let mut v_res_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_1634_ = (leanh::lean_unbox(v_flag_1630_) as u8);
    v_res_1635_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1_spec__6(v_flag_boxed_1634_, v___y_1631_, v___y_1632_);
    leanh::lean_dec(v___y_1632_);
    leanh::lean_dec_ref(v___y_1631_);
    return v_res_1635_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1(
    mut v_00_u03b1_1636_: *mut leanh::LeanObject,
    mut v_flag_1637_: u8,
    mut v_x_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1___redArg(
        v_flag_1637_,
        v_x_1638_,
        v___y_1639_,
        v___y_1640_,
    );
    return v___x_1642_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1___boxed(
    mut v_00_u03b1_1643_: *mut leanh::LeanObject,
    mut v_flag_1644_: *mut leanh::LeanObject,
    mut v_x_1645_: *mut leanh::LeanObject,
    mut v___y_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_1649_: u8 = 0;
    let mut v_res_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_1649_ = (leanh::lean_unbox(v_flag_1644_) as u8);
    v_res_1650_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_withSetOptionIn_spec__1(
        v_00_u03b1_1643_,
        v_flag_boxed_1649_,
        v_x_1645_,
        v___y_1646_,
        v___y_1647_,
    );
    leanh::lean_dec(v___y_1647_);
    leanh::lean_dec_ref(v___y_1646_);
    return v_res_1650_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2(
    mut v_t_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2___redArg(v_t_1651_, v___y_1653_);
    return v___x_1655_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2___boxed(
    mut v_t_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__1_spec__2(v_t_1656_, v___y_1657_, v___y_1658_);
    leanh::lean_dec(v___y_1658_);
    leanh::lean_dec_ref(v___y_1657_);
    return v_res_1660_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4(
    mut v_msgData_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1665_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___redArg(v_msgData_1661_, v___y_1663_);
    return v___x_1665_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4___boxed(
    mut v_msgData_1666_: *mut leanh::LeanObject,
    mut v___y_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__4(v_msgData_1666_, v___y_1667_, v___y_1668_);
    leanh::lean_dec(v___y_1668_);
    leanh::lean_dec_ref(v___y_1667_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2(
    mut v_00_u03b1_1671_: *mut leanh::LeanObject,
    mut v_msg_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___redArg(v_msg_1672_, v___y_1673_, v___y_1674_);
    return v___x_1676_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2___boxed(
    mut v_00_u03b1_1677_: *mut leanh::LeanObject,
    mut v_msg_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2(v_00_u03b1_1677_, v_msg_1678_, v___y_1679_, v___y_1680_);
    leanh::lean_dec(v___y_1680_);
    leanh::lean_dec_ref(v___y_1679_);
    return v_res_1682_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3(
    mut v_00_u03b1_1683_: *mut leanh::LeanObject,
    mut v_optionName_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___redArg(v_optionName_1684_, v___y_1685_, v___y_1686_);
    return v___x_1688_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3___boxed(
    mut v_00_u03b1_1689_: *mut leanh::LeanObject,
    mut v_optionName_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__3(v_00_u03b1_1689_, v_optionName_1690_, v___y_1691_, v___y_1692_);
    leanh::lean_dec(v___y_1692_);
    leanh::lean_dec_ref(v___y_1691_);
    return v_res_1694_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5(
    mut v_msgData_1695_: *mut leanh::LeanObject,
    mut v_macroStack_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___redArg(v_msgData_1695_, v_macroStack_1696_, v___y_1698_);
    return v___x_1700_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5___boxed(
    mut v_msgData_1701_: *mut leanh::LeanObject,
    mut v_macroStack_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1706_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_elabSetOption___at___00Lean_withSetOptionIn_spec__0_spec__2_spec__5(v_msgData_1701_, v_macroStack_1702_, v___y_1703_, v___y_1704_);
    leanh::lean_dec(v___y_1704_);
    leanh::lean_dec_ref(v___y_1703_);
    return v_res_1706_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Basic(builtin);
}