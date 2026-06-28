// Lean compiler output
// Module: Lean.Meta.Match.MatchPatternAttr
// Imports: Lean.Attributes
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_replaceRef};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute,
    runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_isDefinition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Prelude::{lean_array_get, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 64, 91, 109, 97, 116, 99, 104, 95, 112, 97, 116, 116, 101, 114, 110, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 96, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 101, 120, 112, 111, 115, 101, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 97, 116, 99, 104, 95, 112, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject,18380395244438740281 as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanStringObject<125> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 125, m_capacity: 125, m_length: 124, m_data: [109, 97, 114, 107, 32, 116, 104, 97, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 105, 110, 32, 97, 32, 112, 97, 116, 116, 101, 114, 110, 32, 40, 114, 101, 109, 97, 114, 107, 58, 32, 116, 104, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 112, 97, 116, 116, 101, 114, 110, 32, 109, 97, 116, 99, 104, 105, 110, 103, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 119, 105, 108, 108, 32, 117, 110, 102, 111, 108, 100, 32, 116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 41, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [109, 97, 116, 99, 104, 80, 97, 116, 116, 101, 114, 110, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject,3479869179389438886 as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0_value: LeanStringObject<445> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 445, m_capacity: 445, m_length: 444, m_data: [73, 110, 115, 116, 114, 117, 99, 116, 115, 32, 116, 104, 101, 32, 112, 97, 116, 116, 101, 114, 110, 32, 109, 97, 116, 99, 104, 101, 114, 32, 116, 111, 32, 117, 110, 102, 111, 108, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 116, 104, 105, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 10, 10, 66, 121, 32, 100, 101, 102, 97, 117, 108, 116, 44, 32, 111, 110, 108, 121, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 32, 97, 110, 100, 32, 108, 105, 116, 101, 114, 97, 108, 115, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 102, 111, 114, 32, 112, 97, 116, 116, 101, 114, 110, 32, 109, 97, 116, 99, 104, 105, 110, 103, 46, 32, 85, 115, 105, 110, 103, 10, 96, 64, 91, 109, 97, 116, 99, 104, 95, 112, 97, 116, 116, 101, 114, 110, 93, 96, 32, 97, 108, 108, 111, 119, 115, 32, 117, 115, 105, 110, 103, 32, 111, 116, 104, 101, 114, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 44, 32, 97, 115, 32, 108, 111, 110, 103, 32, 97, 115, 32, 116, 104, 101, 121, 32, 101, 118, 101, 110, 116, 117, 97, 108, 108, 121, 32, 114, 101, 100, 117, 99, 101, 32, 116, 111, 10, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 32, 97, 110, 100, 32, 108, 105, 116, 101, 114, 97, 108, 115, 46, 10, 10, 69, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 64, 91, 109, 97, 116, 99, 104, 95, 112, 97, 116, 116, 101, 114, 110, 93, 10, 100, 101, 102, 32, 121, 101, 108, 108, 111, 119, 83, 116, 114, 105, 110, 103, 32, 58, 32, 83, 116, 114, 105, 110, 103, 32, 58, 61, 32, 34, 121, 101, 108, 108, 111, 119, 34, 10, 10, 100, 101, 102, 32, 105, 115, 89, 101, 108, 108, 111, 119, 32, 40, 99, 111, 108, 111, 114, 32, 58, 32, 83, 116, 114, 105, 110, 103, 41, 32, 58, 32, 66, 111, 111, 108, 32, 58, 61, 10, 32, 32, 109, 97, 116, 99, 104, 32, 99, 111, 108, 111, 114, 32, 119, 105, 116, 104, 10, 32, 32, 124, 32, 121, 101, 108, 108, 111, 119, 83, 116, 114, 105, 110, 103, 32, 61, 62, 32, 116, 114, 117, 101, 10, 32, 32, 124, 32, 95, 32, 61, 62, 32, 102, 97, 108, 115, 101, 10, 96, 96, 96, 10, 0]};
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 116 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 116 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___lam__0(
    mut v___y_589_: *mut LeanObject,
    mut v_isExporting_590_: u8,
    mut v___x_591_: *mut LeanObject,
    mut v_a_x3f_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_605_: u8 = 0;
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_613_: u8 = 0;
    let mut v_unused_614_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_594_ = lean_st_ref_take(v___y_589_);
                v_env_595_ = lean_ctor_get(v___x_594_, 0);
                v_nextMacroScope_596_ = lean_ctor_get(v___x_594_, 1);
                v_ngen_597_ = lean_ctor_get(v___x_594_, 2);
                v_auxDeclNGen_598_ = lean_ctor_get(v___x_594_, 3);
                v_traceState_599_ = lean_ctor_get(v___x_594_, 4);
                v_messages_600_ = lean_ctor_get(v___x_594_, 6);
                v_infoState_601_ = lean_ctor_get(v___x_594_, 7);
                v_snapshotTasks_602_ = lean_ctor_get(v___x_594_, 8);
                v_isSharedCheck_613_ = (!lean_is_exclusive(v___x_594_)) as u8;
                if v_isSharedCheck_613_ == 0 {
                    v_unused_614_ = lean_ctor_get(v___x_594_, 5);
                    lean_dec(v_unused_614_);
                    v___x_604_ = v___x_594_;
                    v_isShared_605_ = v_isSharedCheck_613_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_602_);
                    lean_inc(v_infoState_601_);
                    lean_inc(v_messages_600_);
                    lean_inc(v_traceState_599_);
                    lean_inc(v_auxDeclNGen_598_);
                    lean_inc(v_ngen_597_);
                    lean_inc(v_nextMacroScope_596_);
                    lean_inc(v_env_595_);
                    lean_dec(v___x_594_);
                    v___x_604_ = lean_box(0);
                    v_isShared_605_ = v_isSharedCheck_613_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_606_ = l_Lean_Environment_setExporting(v_env_595_, v_isExporting_590_);
                if v_isShared_605_ == 0 {
                    lean_ctor_set(v___x_604_, 5, v___x_591_);
                    lean_ctor_set(v___x_604_, 0, v___x_606_);
                    v___x_608_ = v___x_604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_606_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 1, v_nextMacroScope_596_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 2, v_ngen_597_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 3, v_auxDeclNGen_598_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 4, v_traceState_599_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 5, v___x_591_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 6, v_messages_600_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 7, v_infoState_601_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 8, v_snapshotTasks_602_);
                    v___x_608_ = v_reuseFailAlloc_612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_609_ = lean_st_ref_set(v___y_589_, v___x_608_);
                v___x_610_ = lean_box(0);
                v___x_611_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_611_, 0, v___x_610_);
                return v___x_611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(
    mut v___y_615_: *mut LeanObject,
    mut v_isExporting_616_: *mut LeanObject,
    mut v___x_617_: *mut LeanObject,
    mut v_a_x3f_618_: *mut LeanObject,
    mut v___y_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_620_: u8 = 0;
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_620_ = (lean_unbox(v_isExporting_616_) as u8);
    v_res_621_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_615_, v_isExporting_boxed_620_, v___x_617_, v_a_x3f_618_);
    lean_dec(v_a_x3f_618_);
    lean_dec(v___y_615_);
    return v_res_621_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_622_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    v___x_623_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__0);
    v___x_624_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_624_, 0, v___x_623_);
    return v___x_624_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_625_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__1);
    v___x_626_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_626_, 0, v___x_625_);
    lean_ctor_set(v___x_626_, 1, v___x_625_);
    return v___x_626_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg(
    mut v_x_627_: *mut LeanObject,
    mut v_isExporting_628_: u8,
    mut v___y_629_: *mut LeanObject,
    mut v___y_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_634_: u8 = 0;
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_646_: u8 = 0;
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_unused_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_669_: u8 = 0;
    let mut v_a_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v_unused_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v_unused_683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_632_ = lean_st_ref_get(v___y_630_);
                v_env_633_ = lean_ctor_get(v___x_632_, 0);
                lean_inc_ref(v_env_633_);
                lean_dec(v___x_632_);
                v_isExporting_634_ = lean_ctor_get_uint8(
                    v_env_633_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_633_);
                v___x_635_ = lean_st_ref_take(v___y_630_);
                v_env_636_ = lean_ctor_get(v___x_635_, 0);
                v_nextMacroScope_637_ = lean_ctor_get(v___x_635_, 1);
                v_ngen_638_ = lean_ctor_get(v___x_635_, 2);
                v_auxDeclNGen_639_ = lean_ctor_get(v___x_635_, 3);
                v_traceState_640_ = lean_ctor_get(v___x_635_, 4);
                v_messages_641_ = lean_ctor_get(v___x_635_, 6);
                v_infoState_642_ = lean_ctor_get(v___x_635_, 7);
                v_snapshotTasks_643_ = lean_ctor_get(v___x_635_, 8);
                v_isSharedCheck_682_ = (!lean_is_exclusive(v___x_635_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v_unused_683_ = lean_ctor_get(v___x_635_, 5);
                    lean_dec(v_unused_683_);
                    v___x_645_ = v___x_635_;
                    v_isShared_646_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_643_);
                    lean_inc(v_infoState_642_);
                    lean_inc(v_messages_641_);
                    lean_inc(v_traceState_640_);
                    lean_inc(v_auxDeclNGen_639_);
                    lean_inc(v_ngen_638_);
                    lean_inc(v_nextMacroScope_637_);
                    lean_inc(v_env_636_);
                    lean_dec(v___x_635_);
                    v___x_645_ = lean_box(0);
                    v_isShared_646_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_647_ = l_Lean_Environment_setExporting(v_env_636_, v_isExporting_628_);
                v___x_648_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___closed__2);
                if v_isShared_646_ == 0 {
                    lean_ctor_set(v___x_645_, 5, v___x_648_);
                    lean_ctor_set(v___x_645_, 0, v___x_647_);
                    v___x_650_ = v___x_645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_647_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 1, v_nextMacroScope_637_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 2, v_ngen_638_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 3, v_auxDeclNGen_639_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 4, v_traceState_640_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 5, v___x_648_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 6, v_messages_641_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 7, v_infoState_642_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 8, v_snapshotTasks_643_);
                    v___x_650_ = v_reuseFailAlloc_681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_651_ = lean_st_ref_set(v___y_630_, v___x_650_);
                lean_inc(v___y_630_);
                lean_inc_ref(v___y_629_);
                v_r_652_ = lean_apply_3(v_x_627_, v___y_629_, v___y_630_, lean_box(0));
                if lean_obj_tag(v_r_652_) == 0 {
                    v_a_653_ = lean_ctor_get(v_r_652_, 0);
                    v_isSharedCheck_669_ = (!lean_is_exclusive(v_r_652_)) as u8;
                    if v_isSharedCheck_669_ == 0 {
                        v___x_655_ = v_r_652_;
                        v_isShared_656_ = v_isSharedCheck_669_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_653_);
                        lean_dec(v_r_652_);
                        v___x_655_ = lean_box(0);
                        v_isShared_656_ = v_isSharedCheck_669_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_670_ = lean_ctor_get(v_r_652_, 0);
                    lean_inc(v_a_670_);
                    lean_dec_ref_known(v_r_652_, 1);
                    v___x_671_ = lean_box(0);
                    v___x_672_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_630_, v_isExporting_634_, v___x_648_, v___x_671_);
                    v_isSharedCheck_679_ = (!lean_is_exclusive(v___x_672_)) as u8;
                    if v_isSharedCheck_679_ == 0 {
                        v_unused_680_ = lean_ctor_get(v___x_672_, 0);
                        lean_dec(v_unused_680_);
                        v___x_674_ = v___x_672_;
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_672_);
                        v___x_674_ = lean_box(0);
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_653_);
                if v_isShared_656_ == 0 {
                    lean_ctor_set_tag(v___x_655_, 1);
                    v___x_658_ = v___x_655_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_653_);
                    v___x_658_ = v_reuseFailAlloc_668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_659_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_630_, v_isExporting_634_, v___x_648_, v___x_658_);
                lean_dec_ref(v___x_658_);
                v_isSharedCheck_666_ = (!lean_is_exclusive(v___x_659_)) as u8;
                if v_isSharedCheck_666_ == 0 {
                    v_unused_667_ = lean_ctor_get(v___x_659_, 0);
                    lean_dec(v_unused_667_);
                    v___x_661_ = v___x_659_;
                    v_isShared_662_ = v_isSharedCheck_666_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_659_);
                    v___x_661_ = lean_box(0);
                    v_isShared_662_ = v_isSharedCheck_666_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_662_ == 0 {
                    lean_ctor_set(v___x_661_, 0, v_a_653_);
                    v___x_664_ = v___x_661_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_653_);
                    v___x_664_ = v_reuseFailAlloc_665_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_664_;
            }
            7 => {
                if v_isShared_675_ == 0 {
                    lean_ctor_set_tag(v___x_674_, 1);
                    lean_ctor_set(v___x_674_, 0, v_a_670_);
                    v___x_677_ = v___x_674_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_670_);
                    v___x_677_ = v_reuseFailAlloc_678_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_x_684_: *mut LeanObject,
    mut v_isExporting_685_: *mut LeanObject,
    mut v___y_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_689_: u8 = 0;
    let mut v_res_690_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_689_ = (lean_unbox(v_isExporting_685_) as u8);
    v_res_690_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg(v_x_684_, v_isExporting_boxed_689_, v___y_686_, v___y_687_);
    lean_dec(v___y_687_);
    lean_dec_ref(v___y_686_);
    return v_res_690_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2(
    mut v_00_u03b1_691_: *mut LeanObject,
    mut v_x_692_: *mut LeanObject,
    mut v_isExporting_693_: u8,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg(v_x_692_, v_isExporting_693_, v___y_694_, v___y_695_);
    return v___x_697_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b1_698_: *mut LeanObject,
    mut v_x_699_: *mut LeanObject,
    mut v_isExporting_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
    mut v___y_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_704_: u8 = 0;
    let mut v_res_705_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_704_ = (lean_unbox(v_isExporting_700_) as u8);
    v_res_705_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2(v_00_u03b1_698_, v_x_699_, v_isExporting_boxed_704_, v___y_701_, v___y_702_);
    lean_dec(v___y_702_);
    lean_dec_ref(v___y_701_);
    return v_res_705_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_706_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_707_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__0);
    v___x_708_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_708_, 0, v___x_707_);
    return v___x_708_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1);
    v___x_710_ = lean_unsigned_to_nat(0);
    v___x_711_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_711_, 0, v___x_710_);
    lean_ctor_set(v___x_711_, 1, v___x_710_);
    lean_ctor_set(v___x_711_, 2, v___x_710_);
    lean_ctor_set(v___x_711_, 3, v___x_710_);
    lean_ctor_set(v___x_711_, 4, v___x_709_);
    lean_ctor_set(v___x_711_, 5, v___x_709_);
    lean_ctor_set(v___x_711_, 6, v___x_709_);
    lean_ctor_set(v___x_711_, 7, v___x_709_);
    lean_ctor_set(v___x_711_, 8, v___x_709_);
    lean_ctor_set(v___x_711_, 9, v___x_709_);
    return v___x_711_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = lean_unsigned_to_nat(32);
    v___x_713_ = lean_mk_empty_array_with_capacity(v___x_712_);
    v___x_714_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_714_, 0, v___x_713_);
    return v___x_714_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = 5usize;
    v___x_716_ = lean_unsigned_to_nat(0);
    v___x_717_ = lean_unsigned_to_nat(32);
    v___x_718_ = lean_mk_empty_array_with_capacity(v___x_717_);
    v___x_719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__3);
    v___x_720_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_720_, 0, v___x_719_);
    lean_ctor_set(v___x_720_, 1, v___x_718_);
    lean_ctor_set(v___x_720_, 2, v___x_716_);
    lean_ctor_set(v___x_720_, 3, v___x_716_);
    lean_ctor_set_usize(v___x_720_, 4, v___x_715_);
    return v___x_720_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = lean_box(1);
    v___x_722_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__4);
    v___x_723_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__1);
    v___x_724_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_724_, 0, v___x_723_);
    lean_ctor_set(v___x_724_, 1, v___x_722_);
    lean_ctor_set(v___x_724_, 2, v___x_721_);
    return v___x_724_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2(
    mut v_msgData_725_: *mut LeanObject,
    mut v___y_726_: *mut LeanObject,
    mut v___y_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = lean_st_ref_get(v___y_727_);
    v_env_730_ = lean_ctor_get(v___x_729_, 0);
    lean_inc_ref(v_env_730_);
    lean_dec(v___x_729_);
    v_options_731_ = lean_ctor_get(v___y_726_, 2);
    v___x_732_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2);
    v___x_733_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5);
    lean_inc_ref(v_options_731_);
    v___x_734_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_734_, 0, v_env_730_);
    lean_ctor_set(v___x_734_, 1, v___x_732_);
    lean_ctor_set(v___x_734_, 2, v___x_733_);
    lean_ctor_set(v___x_734_, 3, v_options_731_);
    v___x_735_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_735_, 0, v___x_734_);
    lean_ctor_set(v___x_735_, 1, v_msgData_725_);
    v___x_736_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_736_, 0, v___x_735_);
    return v___x_736_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_msgData_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_741_: *mut LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2(v_msgData_737_, v___y_738_, v___y_739_);
    lean_dec(v___y_739_);
    lean_dec_ref(v___y_738_);
    return v_res_741_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___redArg(
    mut v_msg_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_751_: u8 = 0;
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_746_ = lean_ctor_get(v___y_743_, 5);
                v___x_747_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2(v_msg_742_, v___y_743_, v___y_744_);
                v_a_748_ = lean_ctor_get(v___x_747_, 0);
                v_isSharedCheck_756_ = (!lean_is_exclusive(v___x_747_)) as u8;
                if v_isSharedCheck_756_ == 0 {
                    v___x_750_ = v___x_747_;
                    v_isShared_751_ = v_isSharedCheck_756_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_748_);
                    lean_dec(v___x_747_);
                    v___x_750_ = lean_box(0);
                    v_isShared_751_ = v_isSharedCheck_756_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_746_);
                v___x_752_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_752_, 0, v_ref_746_);
                lean_ctor_set(v___x_752_, 1, v_a_748_);
                if v_isShared_751_ == 0 {
                    lean_ctor_set_tag(v___x_750_, 1);
                    lean_ctor_set(v___x_750_, 0, v___x_752_);
                    v___x_754_ = v___x_750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
                    v___x_754_ = v_reuseFailAlloc_755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_msg_757_: *mut LeanObject,
    mut v___y_758_: *mut LeanObject,
    mut v___y_759_: *mut LeanObject,
    mut v___y_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_761_: *mut LeanObject = core::ptr::null_mut();
    v_res_761_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___redArg(v_msg_757_, v___y_758_, v___y_759_);
    lean_dec(v___y_759_);
    lean_dec_ref(v___y_758_);
    return v_res_761_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7___redArg(
    mut v_ref_762_: *mut LeanObject,
    mut v_msg_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_779_: u8 = 0;
    let mut v_cancelTk_x3f_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_781_: u8 = 0;
    let mut v_inheritedTraceOptions_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_767_ = lean_ctor_get(v___y_764_, 0);
    v_fileMap_768_ = lean_ctor_get(v___y_764_, 1);
    v_options_769_ = lean_ctor_get(v___y_764_, 2);
    v_currRecDepth_770_ = lean_ctor_get(v___y_764_, 3);
    v_maxRecDepth_771_ = lean_ctor_get(v___y_764_, 4);
    v_ref_772_ = lean_ctor_get(v___y_764_, 5);
    v_currNamespace_773_ = lean_ctor_get(v___y_764_, 6);
    v_openDecls_774_ = lean_ctor_get(v___y_764_, 7);
    v_initHeartbeats_775_ = lean_ctor_get(v___y_764_, 8);
    v_maxHeartbeats_776_ = lean_ctor_get(v___y_764_, 9);
    v_quotContext_777_ = lean_ctor_get(v___y_764_, 10);
    v_currMacroScope_778_ = lean_ctor_get(v___y_764_, 11);
    v_diag_779_ = lean_ctor_get_uint8(
        v___y_764_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_780_ = lean_ctor_get(v___y_764_, 12);
    v_suppressElabErrors_781_ = lean_ctor_get_uint8(
        v___y_764_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_782_ = lean_ctor_get(v___y_764_, 13);
    v_ref_783_ = l_Lean_replaceRef(v_ref_762_, v_ref_772_);
    lean_inc_ref(v_inheritedTraceOptions_782_);
    lean_inc(v_cancelTk_x3f_780_);
    lean_inc(v_currMacroScope_778_);
    lean_inc(v_quotContext_777_);
    lean_inc(v_maxHeartbeats_776_);
    lean_inc(v_initHeartbeats_775_);
    lean_inc(v_openDecls_774_);
    lean_inc(v_currNamespace_773_);
    lean_inc(v_maxRecDepth_771_);
    lean_inc(v_currRecDepth_770_);
    lean_inc_ref(v_options_769_);
    lean_inc_ref(v_fileMap_768_);
    lean_inc_ref(v_fileName_767_);
    v___x_784_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_784_, 0, v_fileName_767_);
    lean_ctor_set(v___x_784_, 1, v_fileMap_768_);
    lean_ctor_set(v___x_784_, 2, v_options_769_);
    lean_ctor_set(v___x_784_, 3, v_currRecDepth_770_);
    lean_ctor_set(v___x_784_, 4, v_maxRecDepth_771_);
    lean_ctor_set(v___x_784_, 5, v_ref_783_);
    lean_ctor_set(v___x_784_, 6, v_currNamespace_773_);
    lean_ctor_set(v___x_784_, 7, v_openDecls_774_);
    lean_ctor_set(v___x_784_, 8, v_initHeartbeats_775_);
    lean_ctor_set(v___x_784_, 9, v_maxHeartbeats_776_);
    lean_ctor_set(v___x_784_, 10, v_quotContext_777_);
    lean_ctor_set(v___x_784_, 11, v_currMacroScope_778_);
    lean_ctor_set(v___x_784_, 12, v_cancelTk_x3f_780_);
    lean_ctor_set(v___x_784_, 13, v_inheritedTraceOptions_782_);
    lean_ctor_set_uint8(
        v___x_784_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_779_,
    );
    lean_ctor_set_uint8(
        v___x_784_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_781_,
    );
    v___x_785_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___redArg(v_msg_763_, v___x_784_, v___y_765_);
    lean_dec_ref_known(v___x_784_, 14);
    return v___x_785_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_ref_786_: *mut LeanObject,
    mut v_msg_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
    mut v___y_789_: *mut LeanObject,
    mut v___y_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_786_, v_msg_787_, v___y_788_, v___y_789_);
    lean_dec(v___y_789_);
    lean_dec_ref(v___y_788_);
    lean_dec(v_ref_786_);
    return v_res_791_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0;
    v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
    return v___x_794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___x_796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2;
    v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
    return v___x_797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4;
    v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
    return v___x_800_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
    return v___x_803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    v___x_805_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
    return v___x_806_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    v___x_808_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
    return v___x_809_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
    return v___x_812_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(
    mut v_msg_813_: *mut LeanObject,
    mut v_declHint_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: u8 = 0;
    let mut v_isExporting_820_: u8 = 0;
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_842_: u8 = 0;
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_817_ = lean_st_ref_get(v___y_815_);
                v_env_818_ = lean_ctor_get(v___x_817_, 0);
                lean_inc_ref(v_env_818_);
                lean_dec(v___x_817_);
                v___x_819_ = l_Lean_Name_isAnonymous(v_declHint_814_);
                if v___x_819_ == 0 {
                    v_isExporting_820_ = lean_ctor_get_uint8(
                        v_env_818_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_820_ == 0 {
                        lean_dec_ref(v_env_818_);
                        lean_dec(v_declHint_814_);
                        v___x_821_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_821_, 0, v_msg_813_);
                        return v___x_821_;
                    } else {
                        lean_inc_ref(v_env_818_);
                        v___x_822_ = l_Lean_Environment_setExporting(v_env_818_, v___x_819_);
                        lean_inc(v_declHint_814_);
                        lean_inc_ref(v___x_822_);
                        v___x_823_ = l_Lean_Environment_contains(
                            v___x_822_,
                            v_declHint_814_,
                            v_isExporting_820_,
                        );
                        if v___x_823_ == 0 {
                            lean_dec_ref(v___x_822_);
                            lean_dec_ref(v_env_818_);
                            lean_dec(v_declHint_814_);
                            v___x_824_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_824_, 0, v_msg_813_);
                            return v___x_824_;
                        } else {
                            v___x_825_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__2);
                            v___x_826_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1_spec__2___closed__5);
                            v___x_827_ = l_Lean_Options_empty;
                            v___x_828_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_828_, 0, v___x_822_);
                            lean_ctor_set(v___x_828_, 1, v___x_825_);
                            lean_ctor_set(v___x_828_, 2, v___x_826_);
                            lean_ctor_set(v___x_828_, 3, v___x_827_);
                            lean_inc(v_declHint_814_);
                            v___x_829_ =
                                l_Lean_MessageData_ofConstName(v_declHint_814_, v___x_819_);
                            v_c_830_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_830_, 0, v___x_828_);
                            lean_ctor_set(v_c_830_, 1, v___x_829_);
                            v___x_831_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_818_, v_declHint_814_);
                            if lean_obj_tag(v___x_831_) == 0 {
                                lean_dec_ref(v_env_818_);
                                lean_dec(v_declHint_814_);
                                v___x_832_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
                                v___x_833_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_833_, 0, v___x_832_);
                                lean_ctor_set(v___x_833_, 1, v_c_830_);
                                v___x_834_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
                                v___x_835_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_835_, 0, v___x_833_);
                                lean_ctor_set(v___x_835_, 1, v___x_834_);
                                v___x_836_ = l_Lean_MessageData_note(v___x_835_);
                                v___x_837_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_837_, 0, v_msg_813_);
                                lean_ctor_set(v___x_837_, 1, v___x_836_);
                                v___x_838_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_838_, 0, v___x_837_);
                                return v___x_838_;
                            } else {
                                v_val_839_ = lean_ctor_get(v___x_831_, 0);
                                v_isSharedCheck_874_ = (!lean_is_exclusive(v___x_831_)) as u8;
                                if v_isSharedCheck_874_ == 0 {
                                    v___x_841_ = v___x_831_;
                                    v_isShared_842_ = v_isSharedCheck_874_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_839_);
                                    lean_dec(v___x_831_);
                                    v___x_841_ = lean_box(0);
                                    v_isShared_842_ = v_isSharedCheck_874_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_818_);
                    lean_dec(v_declHint_814_);
                    v___x_875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_875_, 0, v_msg_813_);
                    return v___x_875_;
                }
            }
            1 => {
                v___x_843_ = lean_box(0);
                v___x_844_ = l_Lean_Environment_header(v_env_818_);
                lean_dec_ref(v_env_818_);
                v___x_845_ = l_Lean_EnvironmentHeader_moduleNames(v___x_844_);
                v_mod_846_ = lean_array_get(v___x_843_, v___x_845_, v_val_839_);
                lean_dec(v_val_839_);
                lean_dec_ref(v___x_845_);
                v___x_847_ = l_Lean_isPrivateName(v_declHint_814_);
                lean_dec(v_declHint_814_);
                if v___x_847_ == 0 {
                    v___x_848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
                    v___x_849_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_849_, 0, v___x_848_);
                    lean_ctor_set(v___x_849_, 1, v_c_830_);
                    v___x_850_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_851_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_851_, 0, v___x_849_);
                    lean_ctor_set(v___x_851_, 1, v___x_850_);
                    v___x_852_ = l_Lean_MessageData_ofName(v_mod_846_);
                    v___x_853_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_853_, 0, v___x_851_);
                    lean_ctor_set(v___x_853_, 1, v___x_852_);
                    v___x_854_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
                    v___x_855_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_855_, 0, v___x_853_);
                    lean_ctor_set(v___x_855_, 1, v___x_854_);
                    v___x_856_ = l_Lean_MessageData_note(v___x_855_);
                    v___x_857_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_857_, 0, v_msg_813_);
                    lean_ctor_set(v___x_857_, 1, v___x_856_);
                    if v_isShared_842_ == 0 {
                        lean_ctor_set_tag(v___x_841_, 0);
                        lean_ctor_set(v___x_841_, 0, v___x_857_);
                        v___x_859_ = v___x_841_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
                        v___x_859_ = v_reuseFailAlloc_860_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_861_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
                    v___x_862_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_862_, 0, v___x_861_);
                    lean_ctor_set(v___x_862_, 1, v_c_830_);
                    v___x_863_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_864_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_864_, 0, v___x_862_);
                    lean_ctor_set(v___x_864_, 1, v___x_863_);
                    v___x_865_ = l_Lean_MessageData_ofName(v_mod_846_);
                    v___x_866_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_866_, 0, v___x_864_);
                    lean_ctor_set(v___x_866_, 1, v___x_865_);
                    v___x_867_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_868_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_868_, 0, v___x_866_);
                    lean_ctor_set(v___x_868_, 1, v___x_867_);
                    v___x_869_ = l_Lean_MessageData_note(v___x_868_);
                    v___x_870_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_870_, 0, v_msg_813_);
                    lean_ctor_set(v___x_870_, 1, v___x_869_);
                    if v_isShared_842_ == 0 {
                        lean_ctor_set_tag(v___x_841_, 0);
                        lean_ctor_set(v___x_841_, 0, v___x_870_);
                        v___x_872_ = v___x_841_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
                        v___x_872_ = v_reuseFailAlloc_873_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_859_;
            }
            3 => {
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_876_: *mut LeanObject,
    mut v_declHint_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
    mut v___y_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_880_: *mut LeanObject = core::ptr::null_mut();
    v_res_880_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_876_, v_declHint_877_, v___y_878_);
    lean_dec(v___y_878_);
    return v_res_880_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_msg_881_: *mut LeanObject,
    mut v_declHint_882_: *mut LeanObject,
    mut v___y_883_: *mut LeanObject,
    mut v___y_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_881_, v_declHint_882_, v___y_884_);
                v_a_887_ = lean_ctor_get(v___x_886_, 0);
                v_isSharedCheck_896_ = (!lean_is_exclusive(v___x_886_)) as u8;
                if v_isSharedCheck_896_ == 0 {
                    v___x_889_ = v___x_886_;
                    v_isShared_890_ = v_isSharedCheck_896_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_887_);
                    lean_dec(v___x_886_);
                    v___x_889_ = lean_box(0);
                    v_isShared_890_ = v_isSharedCheck_896_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_891_ = l_Lean_unknownIdentifierMessageTag;
                v___x_892_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_892_, 0, v___x_891_);
                lean_ctor_set(v___x_892_, 1, v_a_887_);
                if v_isShared_890_ == 0 {
                    lean_ctor_set(v___x_889_, 0, v___x_892_);
                    v___x_894_ = v___x_889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
                    v___x_894_ = v_reuseFailAlloc_895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6___boxed(
    mut v_msg_897_: *mut LeanObject,
    mut v_declHint_898_: *mut LeanObject,
    mut v___y_899_: *mut LeanObject,
    mut v___y_900_: *mut LeanObject,
    mut v___y_901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_902_: *mut LeanObject = core::ptr::null_mut();
    v_res_902_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_897_, v_declHint_898_, v___y_899_, v___y_900_);
    lean_dec(v___y_900_);
    lean_dec_ref(v___y_899_);
    return v_res_902_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_ref_903_: *mut LeanObject,
    mut v_msg_904_: *mut LeanObject,
    mut v_declHint_905_: *mut LeanObject,
    mut v___y_906_: *mut LeanObject,
    mut v___y_907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_909_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_904_, v_declHint_905_, v___y_906_, v___y_907_);
    v_a_910_ = lean_ctor_get(v___x_909_, 0);
    lean_inc(v_a_910_);
    lean_dec_ref(v___x_909_);
    v___x_911_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_903_, v_a_910_, v___y_906_, v___y_907_);
    return v___x_911_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_ref_912_: *mut LeanObject,
    mut v_msg_913_: *mut LeanObject,
    mut v_declHint_914_: *mut LeanObject,
    mut v___y_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_918_: *mut LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_ref_912_, v_msg_913_, v_declHint_914_, v___y_915_, v___y_916_);
    lean_dec(v___y_916_);
    lean_dec_ref(v___y_915_);
    lean_dec(v_ref_912_);
    return v_res_918_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
    return v___x_921_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    v___x_923_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
    return v___x_924_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_ref_925_: *mut LeanObject,
    mut v_constName_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
    mut v___y_928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    v___x_930_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_931_ = 0;
    lean_inc(v_constName_926_);
    v___x_932_ = l_Lean_MessageData_ofConstName(v_constName_926_, v___x_931_);
    v___x_933_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_933_, 0, v___x_930_);
    lean_ctor_set(v___x_933_, 1, v___x_932_);
    v___x_934_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_935_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_935_, 0, v___x_933_);
    lean_ctor_set(v___x_935_, 1, v___x_934_);
    v___x_936_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_ref_925_, v___x_935_, v_constName_926_, v___y_927_, v___y_928_);
    return v___x_936_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_937_: *mut LeanObject,
    mut v_constName_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
    mut v___y_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_942_: *mut LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ref_937_, v_constName_938_, v___y_939_, v___y_940_);
    lean_dec(v___y_940_);
    lean_dec_ref(v___y_939_);
    lean_dec(v_ref_937_);
    return v_res_942_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_constName_943_: *mut LeanObject,
    mut v___y_944_: *mut LeanObject,
    mut v___y_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v_ref_947_ = lean_ctor_get(v___y_944_, 5);
    v___x_948_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ref_947_, v_constName_943_, v___y_944_, v___y_945_);
    return v___x_948_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_constName_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
    mut v___y_951_: *mut LeanObject,
    mut v___y_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_953_: *mut LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_949_, v___y_950_, v___y_951_);
    lean_dec(v___y_951_);
    lean_dec_ref(v___y_950_);
    return v_res_953_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0(
    mut v_constName_954_: *mut LeanObject,
    mut v___y_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_966_: u8 = 0;
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_958_ = lean_st_ref_get(v___y_956_);
                v_env_959_ = lean_ctor_get(v___x_958_, 0);
                lean_inc_ref(v_env_959_);
                lean_dec(v___x_958_);
                v___x_960_ = 0;
                lean_inc(v_constName_954_);
                v___x_961_ = l_Lean_Environment_find_x3f(v_env_959_, v_constName_954_, v___x_960_);
                if lean_obj_tag(v___x_961_) == 0 {
                    v___x_962_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_954_, v___y_955_, v___y_956_);
                    return v___x_962_;
                } else {
                    lean_dec(v_constName_954_);
                    v_val_963_ = lean_ctor_get(v___x_961_, 0);
                    v_isSharedCheck_970_ = (!lean_is_exclusive(v___x_961_)) as u8;
                    if v_isSharedCheck_970_ == 0 {
                        v___x_965_ = v___x_961_;
                        v_isShared_966_ = v_isSharedCheck_970_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_963_);
                        lean_dec(v___x_961_);
                        v___x_965_ = lean_box(0);
                        v_isShared_966_ = v_isSharedCheck_970_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_966_ == 0 {
                    lean_ctor_set_tag(v___x_965_, 0);
                    v___x_968_ = v___x_965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_969_, 0, v_val_963_);
                    v___x_968_ = v_reuseFailAlloc_969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0___boxed(
    mut v_constName_971_: *mut LeanObject,
    mut v___y_972_: *mut LeanObject,
    mut v___y_973_: *mut LeanObject,
    mut v___y_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_975_: *mut LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0(v_constName_971_, v___y_972_, v___y_973_);
    lean_dec(v___y_973_);
    lean_dec_ref(v___y_972_);
    return v_res_975_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_977_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
    return v___x_978_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_980_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
    return v___x_981_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_(
    mut v_declName_982_: *mut LeanObject,
    mut v___y_983_: *mut LeanObject,
    mut v___y_984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: u8 = 0;
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1002_: u8 = 0;
    let mut v_a_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1006_: u8 = 0;
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_982_);
                v___x_986_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0(v_declName_982_, v___y_983_, v___y_984_);
                if lean_obj_tag(v___x_986_) == 0 {
                    v_a_987_ = lean_ctor_get(v___x_986_, 0);
                    v_isSharedCheck_1002_ = (!lean_is_exclusive(v___x_986_)) as u8;
                    if v_isSharedCheck_1002_ == 0 {
                        v___x_989_ = v___x_986_;
                        v_isShared_990_ = v_isSharedCheck_1002_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_987_);
                        lean_dec(v___x_986_);
                        v___x_989_ = lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_1002_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_982_);
                    v_a_1003_ = lean_ctor_get(v___x_986_, 0);
                    v_isSharedCheck_1010_ = (!lean_is_exclusive(v___x_986_)) as u8;
                    if v_isSharedCheck_1010_ == 0 {
                        v___x_1005_ = v___x_986_;
                        v_isShared_1006_ = v_isSharedCheck_1010_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1003_);
                        lean_dec(v___x_986_);
                        v___x_1005_ = lean_box(0);
                        v_isShared_1006_ = v_isSharedCheck_1010_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_991_ = l_Lean_ConstantInfo_isDefinition(v_a_987_);
                lean_dec(v_a_987_);
                if v___x_991_ == 0 {
                    lean_del_object(v___x_989_);
                    v___x_992_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_);
                    v___x_993_ = l_Lean_MessageData_ofConstName(v_declName_982_, v___x_991_);
                    v___x_994_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_994_, 0, v___x_992_);
                    lean_ctor_set(v___x_994_, 1, v___x_993_);
                    v___x_995_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_);
                    v___x_996_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_996_, 0, v___x_994_);
                    lean_ctor_set(v___x_996_, 1, v___x_995_);
                    v___x_997_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___redArg(v___x_996_, v___y_983_, v___y_984_);
                    return v___x_997_;
                } else {
                    lean_dec(v_declName_982_);
                    v___x_998_ = lean_box(0);
                    if v_isShared_990_ == 0 {
                        lean_ctor_set(v___x_989_, 0, v___x_998_);
                        v___x_1000_ = v___x_989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
                        v___x_1000_ = v_reuseFailAlloc_1001_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1000_;
            }
            3 => {
                if v_isShared_1006_ == 0 {
                    v___x_1008_ = v___x_1005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
                    v___x_1008_ = v_reuseFailAlloc_1009_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2____boxed(
    mut v_declName_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
    mut v___y_1013_: *mut LeanObject,
    mut v___y_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1015_: *mut LeanObject = core::ptr::null_mut();
    v_res_1015_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_(v_declName_1011_, v___y_1012_, v___y_1013_);
    lean_dec(v___y_1013_);
    lean_dec_ref(v___y_1012_);
    return v_res_1015_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_(
    mut v_declName_1016_: *mut LeanObject,
    mut v___y_1017_: *mut LeanObject,
    mut v___y_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    lean_inc(v_declName_1016_);
    v___f_1020_ = lean_alloc_closure(l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_1020_, 0, v_declName_1016_);
    v___x_1021_ = l_Lean_isPrivateName(v_declName_1016_);
    lean_dec(v_declName_1016_);
    if v___x_1021_ == 0 {
        let mut v___x_1022_: u8 = 0;
        let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
        v___x_1022_ = 1;
        v___x_1023_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg(v___f_1020_, v___x_1022_, v___y_1017_, v___y_1018_);
        return v___x_1023_;
    } else {
        let mut v___x_1024_: u8 = 0;
        let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
        v___x_1024_ = 0;
        v___x_1025_ = l_Lean_withExporting___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__2___redArg(v___f_1020_, v___x_1024_, v___y_1017_, v___y_1018_);
        return v___x_1025_;
    }
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2____boxed(
    mut v_declName_1026_: *mut LeanObject,
    mut v___y_1027_: *mut LeanObject,
    mut v___y_1028_: *mut LeanObject,
    mut v___y_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_(v_declName_1026_, v___y_1027_, v___y_1028_);
    lean_dec(v___y_1028_);
    lean_dec_ref(v___y_1027_);
    return v_res_1030_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    v___f_1042_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_1043_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_1044_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_1045_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_1046_ = 0;
    v___x_1047_ = lean_box(2);
    v___x_1048_ = l_Lean_registerTagAttribute(
        v___x_1043_,
        v___x_1044_,
        v___f_1042_,
        v___x_1045_,
        v___x_1046_,
        v___x_1047_,
    );
    return v___x_1048_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2____boxed(
    mut v_a_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_();
    return v_res_1050_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_1051_: *mut LeanObject,
    mut v_msg_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    v___x_1056_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___redArg(v_msg_1052_, v___y_1053_, v___y_1054_);
    return v___x_1056_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_1057_: *mut LeanObject,
    mut v_msg_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
    mut v___y_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__1(v_00_u03b1_1057_, v_msg_1058_, v___y_1059_, v___y_1060_);
    lean_dec(v___y_1060_);
    lean_dec_ref(v___y_1059_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_1063_: *mut LeanObject,
    mut v_constName_1064_: *mut LeanObject,
    mut v___y_1065_: *mut LeanObject,
    mut v___y_1066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_1064_, v___y_1065_, v___y_1066_);
    return v___x_1068_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_1069_: *mut LeanObject,
    mut v_constName_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1069_, v_constName_1070_, v___y_1071_, v___y_1072_);
    lean_dec(v___y_1072_);
    lean_dec_ref(v___y_1071_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_00_u03b1_1075_: *mut LeanObject,
    mut v_ref_1076_: *mut LeanObject,
    mut v_constName_1077_: *mut LeanObject,
    mut v___y_1078_: *mut LeanObject,
    mut v___y_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ref_1076_, v_constName_1077_, v___y_1078_, v___y_1079_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_1082_: *mut LeanObject,
    mut v_ref_1083_: *mut LeanObject,
    mut v_constName_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
    mut v___y_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1088_: *mut LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b1_1082_, v_ref_1083_, v_constName_1084_, v___y_1085_, v___y_1086_);
    lean_dec(v___y_1086_);
    lean_dec_ref(v___y_1085_);
    lean_dec(v_ref_1083_);
    return v_res_1088_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b1_1089_: *mut LeanObject,
    mut v_ref_1090_: *mut LeanObject,
    mut v_msg_1091_: *mut LeanObject,
    mut v_declHint_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    v___x_1096_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1090_, v_msg_1091_, v_declHint_1092_, v___y_1093_, v___y_1094_);
    return v___x_1096_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b1_1097_: *mut LeanObject,
    mut v_ref_1098_: *mut LeanObject,
    mut v_msg_1099_: *mut LeanObject,
    mut v_declHint_1100_: *mut LeanObject,
    mut v___y_1101_: *mut LeanObject,
    mut v___y_1102_: *mut LeanObject,
    mut v___y_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1104_: *mut LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_00_u03b1_1097_, v_ref_1098_, v_msg_1099_, v_declHint_1100_, v___y_1101_, v___y_1102_);
    lean_dec(v___y_1102_);
    lean_dec_ref(v___y_1101_);
    lean_dec(v_ref_1098_);
    return v_res_1104_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(
    mut v_msg_1105_: *mut LeanObject,
    mut v_declHint_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1105_, v_declHint_1106_, v___y_1108_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(
    mut v_msg_1111_: *mut LeanObject,
    mut v_declHint_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
    mut v___y_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1116_: *mut LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_1111_, v_declHint_1112_, v___y_1113_, v___y_1114_);
    lean_dec(v___y_1114_);
    lean_dec_ref(v___y_1113_);
    return v_res_1116_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7(
    mut v_00_u03b1_1117_: *mut LeanObject,
    mut v_ref_1118_: *mut LeanObject,
    mut v_msg_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1118_, v_msg_1119_, v___y_1120_, v___y_1121_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_1124_: *mut LeanObject,
    mut v_ref_1125_: *mut LeanObject,
    mut v_msg_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_1124_, v_ref_1125_, v_msg_1126_, v___y_1127_, v___y_1128_);
    lean_dec(v___y_1128_);
    lean_dec_ref(v___y_1127_);
    lean_dec(v_ref_1125_);
    return v_res_1130_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v___x_1133_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_1134_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0;
    v___x_1135_ = l_Lean_addBuiltinDocString(v___x_1133_, v___x_1134_);
    return v___x_1135_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___boxed(
    mut v_a_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
    v_res_1137_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1();
    return v_res_1137_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1164_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_;
    v___x_1165_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6;
    v___x_1166_ = l_Lean_addBuiltinDeclarationRanges(v___x_1164_, v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___boxed(
    mut v_a_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1168_: *mut LeanObject = core::ptr::null_mut();
    v_res_1168_ = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3();
    return v_res_1168_;
}
pub unsafe fn lean_has_match_pattern_attribute(
    mut v_env_1169_: *mut LeanObject,
    mut v_n_1170_: *mut LeanObject,
) -> u8 {
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: u8 = 0;
    v___x_1171_ = l_Lean_matchPatternAttr;
    v___x_1172_ = l_Lean_TagAttribute_hasTag(v___x_1171_, v_env_1169_, v_n_1170_);
    return v___x_1172_;
}
pub unsafe fn l_Lean_hasMatchPatternAttribute___boxed(
    mut v_env_1173_: *mut LeanObject,
    mut v_n_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1175_: u8 = 0;
    let mut v_r_1176_: *mut LeanObject = core::ptr::null_mut();
    v_res_1175_ = lean_has_match_pattern_attribute(v_env_1173_, v_n_1174_);
    v_r_1176_ = lean_box((v_res_1175_) as usize);
    return v_r_1176_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MatchPatternAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_initFn_00___x40_Lean_Meta_Match_MatchPatternAttr_2067758803____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_matchPatternAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_matchPatternAttr);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Match_MatchPatternAttr_0__Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MatchPatternAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_MatchPatternAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
}
