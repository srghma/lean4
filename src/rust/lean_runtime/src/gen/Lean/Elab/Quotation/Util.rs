// Lean compiler output
// Module: Lean.Elab.Quotation.Util
// Imports: Lean.Elab.Term
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isIdent, l_Lean_Syntax_isMissing, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_getAntiquotTerm, l_Lean_Syntax_isAntiquot, l_Lean_Syntax_isEscapedAntiquot,
    l_Lean_Syntax_isQuot, l_Lean_Syntax_isTokenAntiquot, l_Lean_Syntax_topDown,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [104, 121, 103, 105, 101, 110, 101, 0]};
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,7940100381430426555 as *mut LeanObject] };
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanStringObject<243> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 243, m_capacity: 243, m_length: 242, m_data: [65, 110, 110, 111, 116, 97, 116, 101, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 105, 110, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 115, 32, 115, 117, 99, 104, 32, 116, 104, 97, 116, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 114, 101, 115, 111, 108, 118, 101, 100, 32, 114, 101, 108, 97, 116, 105, 118, 101, 32, 116, 111, 32, 116, 104, 101, 32, 115, 99, 111, 112, 101, 32, 97, 116, 32, 116, 104, 101, 105, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 44, 32, 110, 111, 116, 32, 116, 104, 97, 116, 32, 97, 116, 32, 116, 104, 101, 105, 114, 32, 101, 118, 101, 110, 116, 117, 97, 108, 32, 117, 115, 101, 47, 101, 120, 112, 97, 110, 115, 105, 111, 110, 44, 32, 116, 111, 32, 97, 118, 111, 105, 100, 32, 97, 99, 99, 105, 100, 101, 110, 116, 97, 108, 32, 99, 97, 112, 116, 117, 114, 105, 110, 103, 46, 32, 78, 111, 116, 101, 32, 116, 104, 97, 116, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 115, 47, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 100, 101, 102, 105, 110, 101, 100, 32, 97, 114, 101, 32, 117, 110, 97, 102, 102, 101, 99, 116, 101, 100, 46, 0]};
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [81, 117, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,7312483928035130638 as *mut LeanObject] };
pub static l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,16976103880728639810 as *mut LeanObject] };
static mut l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0_value) as *mut LeanObject,11985596712582660667 as *mut LeanObject] };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value) as *mut LeanObject;
static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [99, 111, 109, 112, 108, 101, 120, 32, 97, 110, 116, 105, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 110, 111, 116, 32, 97, 108, 108, 111, 119, 101, 100, 32, 104, 101, 114, 101, 0]};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5_value) as *mut LeanObject;
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_Quotation_getPatternVars___closed__0_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_Quotation_getPatternVars___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__0_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_Quotation_getPatternVars___closed__2_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [110, 97, 109, 101, 100, 80, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__2_value)
                as *mut LeanObject,
            5023647044732266145 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_Quotation_getPatternVars___closed__4_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 112, 97, 116, 116, 101, 114,
            110, 32, 105, 110, 32, 115, 121, 110, 116, 97, 120, 32, 109, 97, 116, 99, 104, 0,
        ],
    };
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_getPatternVars___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(
    mut v_name_671_: *mut LeanObject,
    mut v_decl_672_: *mut LeanObject,
    mut v_ref_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_684_: u8 = 0;
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_689_: u8 = 0;
    let mut v_unused_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_694_: u8 = 0;
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_675_ = lean_ctor_get(v_decl_672_, 0);
                v_descr_676_ = lean_ctor_get(v_decl_672_, 1);
                v_deprecation_x3f_677_ = lean_ctor_get(v_decl_672_, 2);
                v___x_678_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_679_ = (lean_unbox(v_defValue_675_) as u8);
                lean_ctor_set_uint8(v___x_678_, 0 as u32, v___x_679_);
                lean_inc(v_deprecation_x3f_677_);
                lean_inc_ref(v_descr_676_);
                lean_inc_n(v_name_671_, 2);
                v___x_680_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_680_, 0, v_name_671_);
                lean_ctor_set(v___x_680_, 1, v_ref_673_);
                lean_ctor_set(v___x_680_, 2, v___x_678_);
                lean_ctor_set(v___x_680_, 3, v_descr_676_);
                lean_ctor_set(v___x_680_, 4, v_deprecation_x3f_677_);
                v___x_681_ = lean_register_option(v_name_671_, v___x_680_);
                if lean_obj_tag(v___x_681_) == 0 {
                    v_isSharedCheck_689_ = (!lean_is_exclusive(v___x_681_)) as u8;
                    if v_isSharedCheck_689_ == 0 {
                        v_unused_690_ = lean_ctor_get(v___x_681_, 0);
                        lean_dec(v_unused_690_);
                        v___x_683_ = v___x_681_;
                        v_isShared_684_ = v_isSharedCheck_689_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_681_);
                        v___x_683_ = lean_box(0);
                        v_isShared_684_ = v_isSharedCheck_689_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_671_);
                    v_a_691_ = lean_ctor_get(v___x_681_, 0);
                    v_isSharedCheck_698_ = (!lean_is_exclusive(v___x_681_)) as u8;
                    if v_isSharedCheck_698_ == 0 {
                        v___x_693_ = v___x_681_;
                        v_isShared_694_ = v_isSharedCheck_698_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_691_);
                        lean_dec(v___x_681_);
                        v___x_693_ = lean_box(0);
                        v_isShared_694_ = v_isSharedCheck_698_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_675_);
                v___x_685_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_685_, 0, v_name_671_);
                lean_ctor_set(v___x_685_, 1, v_defValue_675_);
                if v_isShared_684_ == 0 {
                    lean_ctor_set(v___x_683_, 0, v___x_685_);
                    v___x_687_ = v___x_683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
                    v___x_687_ = v_reuseFailAlloc_688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_687_;
            }
            3 => {
                if v_isShared_694_ == 0 {
                    v___x_696_ = v___x_693_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
                    v___x_696_ = v_reuseFailAlloc_697_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_699_: *mut LeanObject,
    mut v_decl_700_: *mut LeanObject,
    mut v_ref_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(v_name_699_, v_decl_700_, v_ref_701_);
    lean_dec_ref(v_decl_700_);
    return v_res_703_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_;
    v___x_725_ = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_;
    v___x_726_ = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_;
    v___x_727_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(v___x_724_, v___x_725_, v___x_726_);
    return v___x_727_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4____boxed(
    mut v_a_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_729_: *mut LeanObject = core::ptr::null_mut();
    v_res_729_ = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
    return v_res_729_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(
    mut v_msgData_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    v___x_736_ = lean_st_ref_get(v___y_734_);
    v_env_737_ = lean_ctor_get(v___x_736_, 0);
    lean_inc_ref(v_env_737_);
    lean_dec(v___x_736_);
    v___x_738_ = lean_st_ref_get(v___y_732_);
    v_mctx_739_ = lean_ctor_get(v___x_738_, 0);
    lean_inc_ref(v_mctx_739_);
    lean_dec(v___x_738_);
    v_lctx_740_ = lean_ctor_get(v___y_731_, 2);
    v_options_741_ = lean_ctor_get(v___y_733_, 2);
    lean_inc_ref(v_options_741_);
    lean_inc_ref(v_lctx_740_);
    v___x_742_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_742_, 0, v_env_737_);
    lean_ctor_set(v___x_742_, 1, v_mctx_739_);
    lean_ctor_set(v___x_742_, 2, v_lctx_740_);
    lean_ctor_set(v___x_742_, 3, v_options_741_);
    v___x_743_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_743_, 0, v___x_742_);
    lean_ctor_set(v___x_743_, 1, v_msgData_730_);
    v___x_744_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_744_, 0, v___x_743_);
    return v___x_744_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_751_: *mut LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(v_msgData_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
    lean_dec(v___y_749_);
    lean_dec_ref(v___y_748_);
    lean_dec(v___y_747_);
    lean_dec_ref(v___y_746_);
    return v_res_751_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(
    mut v_opts_752_: *mut LeanObject,
    mut v_opt_753_: *mut LeanObject,
) -> u8 {
    let mut v_name_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v_name_754_ = lean_ctor_get(v_opt_753_, 0);
    v_defValue_755_ = lean_ctor_get(v_opt_753_, 1);
    v_map_756_ = lean_ctor_get(v_opts_752_, 0);
    v___x_757_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_756_,
            v_name_754_,
        );
    if lean_obj_tag(v___x_757_) == 0 {
        let mut v___x_758_: u8 = 0;
        v___x_758_ = (lean_unbox(v_defValue_755_) as u8);
        return v___x_758_;
    } else {
        let mut v_val_759_: *mut LeanObject = core::ptr::null_mut();
        v_val_759_ = lean_ctor_get(v___x_757_, 0);
        lean_inc(v_val_759_);
        lean_dec_ref_known(v___x_757_, 1);
        if lean_obj_tag(v_val_759_) == 1 {
            let mut v_v_760_: u8 = 0;
            v_v_760_ = lean_ctor_get_uint8(v_val_759_, 0 as u32);
            lean_dec_ref_known(v_val_759_, 0);
            return v_v_760_;
        } else {
            let mut v___x_761_: u8 = 0;
            lean_dec(v_val_759_);
            v___x_761_ = (lean_unbox(v_defValue_755_) as u8);
            return v___x_761_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_opts_762_: *mut LeanObject,
    mut v_opt_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_764_: u8 = 0;
    let mut v_r_765_: *mut LeanObject = core::ptr::null_mut();
    v_res_764_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(v_opts_762_, v_opt_763_);
    lean_dec_ref(v_opt_763_);
    lean_dec_ref(v_opts_762_);
    v_r_765_ = lean_box((v_res_764_) as usize);
    return v_r_765_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ = lean_box(1);
    v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
    return v___x_767_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2;
    v___x_772_ = l_Lean_MessageData_ofFormat(v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(
    mut v_x_773_: *mut LeanObject,
    mut v_x_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_779_: u8 = 0;
    let mut v_before_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_783_: u8 = 0;
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_796_: u8 = 0;
    let mut v_unused_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_774_) == 0 {
                    return v_x_773_;
                } else {
                    v_head_775_ = lean_ctor_get(v_x_774_, 0);
                    v_tail_776_ = lean_ctor_get(v_x_774_, 1);
                    v_isSharedCheck_798_ = (!lean_is_exclusive(v_x_774_)) as u8;
                    if v_isSharedCheck_798_ == 0 {
                        v___x_778_ = v_x_774_;
                        v_isShared_779_ = v_isSharedCheck_798_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_776_);
                        lean_inc(v_head_775_);
                        lean_dec(v_x_774_);
                        v___x_778_ = lean_box(0);
                        v_isShared_779_ = v_isSharedCheck_798_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_780_ = lean_ctor_get(v_head_775_, 0);
                v_isSharedCheck_796_ = (!lean_is_exclusive(v_head_775_)) as u8;
                if v_isSharedCheck_796_ == 0 {
                    v_unused_797_ = lean_ctor_get(v_head_775_, 1);
                    lean_dec(v_unused_797_);
                    v___x_782_ = v_head_775_;
                    v_isShared_783_ = v_isSharedCheck_796_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_780_);
                    lean_dec(v_head_775_);
                    v___x_782_ = lean_box(0);
                    v_isShared_783_ = v_isSharedCheck_796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_784_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_783_ == 0 {
                    lean_ctor_set_tag(v___x_782_, 7);
                    lean_ctor_set(v___x_782_, 1, v___x_784_);
                    lean_ctor_set(v___x_782_, 0, v_x_773_);
                    v___x_786_ = v___x_782_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_795_, 0, v_x_773_);
                    lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_784_);
                    v___x_786_ = v_reuseFailAlloc_795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_787_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3);
                if v_isShared_779_ == 0 {
                    lean_ctor_set_tag(v___x_778_, 7);
                    lean_ctor_set(v___x_778_, 1, v___x_787_);
                    lean_ctor_set(v___x_778_, 0, v___x_786_);
                    v___x_789_ = v___x_778_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_794_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_786_);
                    lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_787_);
                    v___x_789_ = v_reuseFailAlloc_794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_790_ = l_Lean_MessageData_ofSyntax(v_before_780_);
                v___x_791_ = l_Lean_indentD(v___x_790_);
                v___x_792_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_792_, 0, v___x_789_);
                lean_ctor_set(v___x_792_, 1, v___x_791_);
                v_x_773_ = v___x_792_;
                v_x_774_ = v_tail_776_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_803_ = l_Lean_MessageData_ofFormat(v___x_802_);
    return v___x_803_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_804_: *mut LeanObject,
    mut v_macroStack_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_817_: u8 = 0;
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_829_: u8 = 0;
    let mut v_unused_830_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_808_ = lean_ctor_get(v___y_806_, 2);
                v___x_809_ = l_Lean_Elab_pp_macroStack;
                v___x_810_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(v_options_808_, v___x_809_);
                if v___x_810_ == 0 {
                    lean_dec(v_macroStack_805_);
                    v___x_811_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_811_, 0, v_msgData_804_);
                    return v___x_811_;
                } else {
                    if lean_obj_tag(v_macroStack_805_) == 0 {
                        v___x_812_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_812_, 0, v_msgData_804_);
                        return v___x_812_;
                    } else {
                        v_head_813_ = lean_ctor_get(v_macroStack_805_, 0);
                        lean_inc(v_head_813_);
                        v_after_814_ = lean_ctor_get(v_head_813_, 1);
                        v_isSharedCheck_829_ = (!lean_is_exclusive(v_head_813_)) as u8;
                        if v_isSharedCheck_829_ == 0 {
                            v_unused_830_ = lean_ctor_get(v_head_813_, 0);
                            lean_dec(v_unused_830_);
                            v___x_816_ = v_head_813_;
                            v_isShared_817_ = v_isSharedCheck_829_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_814_);
                            lean_dec(v_head_813_);
                            v___x_816_ = lean_box(0);
                            v_isShared_817_ = v_isSharedCheck_829_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_818_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_817_ == 0 {
                    lean_ctor_set_tag(v___x_816_, 7);
                    lean_ctor_set(v___x_816_, 1, v___x_818_);
                    lean_ctor_set(v___x_816_, 0, v_msgData_804_);
                    v___x_820_ = v___x_816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_828_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_828_, 0, v_msgData_804_);
                    lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_818_);
                    v___x_820_ = v_reuseFailAlloc_828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_821_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_822_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_822_, 0, v___x_820_);
                lean_ctor_set(v___x_822_, 1, v___x_821_);
                v___x_823_ = l_Lean_MessageData_ofSyntax(v_after_814_);
                v___x_824_ = l_Lean_indentD(v___x_823_);
                v_msgData_825_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_825_, 0, v___x_822_);
                lean_ctor_set(v_msgData_825_, 1, v___x_824_);
                v___x_826_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(v_msgData_825_, v_macroStack_805_);
                v___x_827_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_827_, 0, v___x_826_);
                return v___x_827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_831_: *mut LeanObject,
    mut v_macroStack_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_835_: *mut LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_831_, v_macroStack_832_, v___y_833_);
    lean_dec_ref(v___y_833_);
    return v_res_835_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(
    mut v_msg_836_: *mut LeanObject,
    mut v___y_837_: *mut LeanObject,
    mut v___y_838_: *mut LeanObject,
    mut v___y_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_853_: u8 = 0;
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_844_ = lean_ctor_get(v___y_841_, 5);
                v___x_845_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(v_msg_836_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
                v_a_846_ = lean_ctor_get(v___x_845_, 0);
                lean_inc(v_a_846_);
                lean_dec_ref(v___x_845_);
                v_macroStack_847_ = lean_ctor_get(v___y_837_, 1);
                v___x_848_ = l_Lean_Elab_getBetterRef(v_ref_844_, v_macroStack_847_);
                lean_inc(v_macroStack_847_);
                v___x_849_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_a_846_, v_macroStack_847_, v___y_841_);
                v_a_850_ = lean_ctor_get(v___x_849_, 0);
                v_isSharedCheck_858_ = (!lean_is_exclusive(v___x_849_)) as u8;
                if v_isSharedCheck_858_ == 0 {
                    v___x_852_ = v___x_849_;
                    v_isShared_853_ = v_isSharedCheck_858_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_850_);
                    lean_dec(v___x_849_);
                    v___x_852_ = lean_box(0);
                    v_isShared_853_ = v_isSharedCheck_858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_854_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_854_, 0, v___x_848_);
                lean_ctor_set(v___x_854_, 1, v_a_850_);
                if v_isShared_853_ == 0 {
                    lean_ctor_set_tag(v___x_852_, 1);
                    lean_ctor_set(v___x_852_, 0, v___x_854_);
                    v___x_856_ = v___x_852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
                    v___x_856_ = v_reuseFailAlloc_857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg___boxed(
    mut v_msg_859_: *mut LeanObject,
    mut v___y_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_867_: *mut LeanObject = core::ptr::null_mut();
    v_res_867_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
    lean_dec(v___y_865_);
    lean_dec_ref(v___y_864_);
    lean_dec(v___y_863_);
    lean_dec_ref(v___y_862_);
    lean_dec(v___y_861_);
    lean_dec_ref(v___y_860_);
    return v_res_867_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(
    mut v_ref_868_: *mut LeanObject,
    mut v_msg_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_889_: u8 = 0;
    let mut v_cancelTk_x3f_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_891_: u8 = 0;
    let mut v_inheritedTraceOptions_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_877_ = lean_ctor_get(v___y_874_, 0);
    v_fileMap_878_ = lean_ctor_get(v___y_874_, 1);
    v_options_879_ = lean_ctor_get(v___y_874_, 2);
    v_currRecDepth_880_ = lean_ctor_get(v___y_874_, 3);
    v_maxRecDepth_881_ = lean_ctor_get(v___y_874_, 4);
    v_ref_882_ = lean_ctor_get(v___y_874_, 5);
    v_currNamespace_883_ = lean_ctor_get(v___y_874_, 6);
    v_openDecls_884_ = lean_ctor_get(v___y_874_, 7);
    v_initHeartbeats_885_ = lean_ctor_get(v___y_874_, 8);
    v_maxHeartbeats_886_ = lean_ctor_get(v___y_874_, 9);
    v_quotContext_887_ = lean_ctor_get(v___y_874_, 10);
    v_currMacroScope_888_ = lean_ctor_get(v___y_874_, 11);
    v_diag_889_ = lean_ctor_get_uint8(
        v___y_874_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_890_ = lean_ctor_get(v___y_874_, 12);
    v_suppressElabErrors_891_ = lean_ctor_get_uint8(
        v___y_874_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_892_ = lean_ctor_get(v___y_874_, 13);
    v_ref_893_ = l_Lean_replaceRef(v_ref_868_, v_ref_882_);
    lean_inc_ref(v_inheritedTraceOptions_892_);
    lean_inc(v_cancelTk_x3f_890_);
    lean_inc(v_currMacroScope_888_);
    lean_inc(v_quotContext_887_);
    lean_inc(v_maxHeartbeats_886_);
    lean_inc(v_initHeartbeats_885_);
    lean_inc(v_openDecls_884_);
    lean_inc(v_currNamespace_883_);
    lean_inc(v_maxRecDepth_881_);
    lean_inc(v_currRecDepth_880_);
    lean_inc_ref(v_options_879_);
    lean_inc_ref(v_fileMap_878_);
    lean_inc_ref(v_fileName_877_);
    v___x_894_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_894_, 0, v_fileName_877_);
    lean_ctor_set(v___x_894_, 1, v_fileMap_878_);
    lean_ctor_set(v___x_894_, 2, v_options_879_);
    lean_ctor_set(v___x_894_, 3, v_currRecDepth_880_);
    lean_ctor_set(v___x_894_, 4, v_maxRecDepth_881_);
    lean_ctor_set(v___x_894_, 5, v_ref_893_);
    lean_ctor_set(v___x_894_, 6, v_currNamespace_883_);
    lean_ctor_set(v___x_894_, 7, v_openDecls_884_);
    lean_ctor_set(v___x_894_, 8, v_initHeartbeats_885_);
    lean_ctor_set(v___x_894_, 9, v_maxHeartbeats_886_);
    lean_ctor_set(v___x_894_, 10, v_quotContext_887_);
    lean_ctor_set(v___x_894_, 11, v_currMacroScope_888_);
    lean_ctor_set(v___x_894_, 12, v_cancelTk_x3f_890_);
    lean_ctor_set(v___x_894_, 13, v_inheritedTraceOptions_892_);
    lean_ctor_set_uint8(
        v___x_894_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_889_,
    );
    lean_ctor_set_uint8(
        v___x_894_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_891_,
    );
    v___x_895_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___x_894_, v___y_875_);
    lean_dec_ref_known(v___x_894_, 14);
    return v___x_895_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg___boxed(
    mut v_ref_896_: *mut LeanObject,
    mut v_msg_897_: *mut LeanObject,
    mut v___y_898_: *mut LeanObject,
    mut v___y_899_: *mut LeanObject,
    mut v___y_900_: *mut LeanObject,
    mut v___y_901_: *mut LeanObject,
    mut v___y_902_: *mut LeanObject,
    mut v___y_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(
            v_ref_896_, v_msg_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_,
            v___y_903_,
        );
    lean_dec(v___y_903_);
    lean_dec_ref(v___y_902_);
    lean_dec(v___y_901_);
    lean_dec_ref(v___y_900_);
    lean_dec(v___y_899_);
    lean_dec_ref(v___y_898_);
    lean_dec(v_ref_896_);
    return v_res_905_;
}
pub unsafe fn _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6()
-> *mut LeanObject {
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    v___x_917_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5;
    v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
    return v___x_918_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(
    mut v_firstChoiceOnly_919_: u8,
    mut v_stx_920_: *mut LeanObject,
    mut v_b_921_: *mut LeanObject,
    mut v___y_922_: *mut LeanObject,
    mut v___y_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_938_: usize = 0;
    let mut v___x_939_: usize = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v_fst_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_a_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_955_: u8 = 0;
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_959_: u8 = 0;
    let mut v_a_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    let mut v_anti_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut v_ids_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_988_ = l_Lean_Syntax_isAntiquot(v_stx_920_);
                if v___x_988_ == 0 {
                    lean_inc(v_stx_920_);
                    v___x_989_ = l_Lean_Syntax_isTokenAntiquot(v_stx_920_);
                    if v___x_989_ == 0 {
                        v_a_961_ = v_b_921_;
                        state = 7;
                        continue;
                    } else {
                        state = 8;
                        continue;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_931_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_931_, 0, v_b_930_);
                v___x_932_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_932_, 0, v___x_931_);
                return v___x_932_;
            }
            2 => {
                v___x_936_ = lean_box(0);
                v___x_937_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_937_, 0, v___x_936_);
                lean_ctor_set(v___x_937_, 1, v___y_935_);
                v_sz_938_ = lean_array_size(v___y_934_);
                v___x_939_ = 0usize;
                v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_919_, v___y_934_, v_sz_938_, v___x_939_, v___x_937_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
                lean_dec_ref(v___y_934_);
                if lean_obj_tag(v___x_940_) == 0 {
                    v_a_941_ = lean_ctor_get(v___x_940_, 0);
                    v_isSharedCheck_951_ = (!lean_is_exclusive(v___x_940_)) as u8;
                    if v_isSharedCheck_951_ == 0 {
                        v___x_943_ = v___x_940_;
                        v_isShared_944_ = v_isSharedCheck_951_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_941_);
                        lean_dec(v___x_940_);
                        v___x_943_ = lean_box(0);
                        v_isShared_944_ = v_isSharedCheck_951_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_952_ = lean_ctor_get(v___x_940_, 0);
                    v_isSharedCheck_959_ = (!lean_is_exclusive(v___x_940_)) as u8;
                    if v_isSharedCheck_959_ == 0 {
                        v___x_954_ = v___x_940_;
                        v_isShared_955_ = v_isSharedCheck_959_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_952_);
                        lean_dec(v___x_940_);
                        v___x_954_ = lean_box(0);
                        v_isShared_955_ = v_isSharedCheck_959_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_945_ = lean_ctor_get(v_a_941_, 0);
                if lean_obj_tag(v_fst_945_) == 0 {
                    lean_del_object(v___x_943_);
                    v_snd_946_ = lean_ctor_get(v_a_941_, 1);
                    lean_inc(v_snd_946_);
                    lean_dec(v_a_941_);
                    v_b_930_ = v_snd_946_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_fst_945_);
                    lean_dec(v_a_941_);
                    v_val_947_ = lean_ctor_get(v_fst_945_, 0);
                    lean_inc(v_val_947_);
                    lean_dec_ref_known(v_fst_945_, 1);
                    if v_isShared_944_ == 0 {
                        lean_ctor_set(v___x_943_, 0, v_val_947_);
                        v___x_949_ = v___x_943_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_950_, 0, v_val_947_);
                        v___x_949_ = v_reuseFailAlloc_950_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_949_;
            }
            5 => {
                if v_isShared_955_ == 0 {
                    v___x_957_ = v___x_954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
                    v___x_957_ = v_reuseFailAlloc_958_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_957_;
            }
            7 => {
                if lean_obj_tag(v_stx_920_) == 1 {
                    if v_firstChoiceOnly_919_ == 0 {
                        v_args_962_ = lean_ctor_get(v_stx_920_, 2);
                        lean_inc_ref(v_args_962_);
                        lean_dec_ref_known(v_stx_920_, 3);
                        v___y_934_ = v_args_962_;
                        v___y_935_ = v_a_961_;
                        state = 2;
                        continue;
                    } else {
                        v_kind_963_ = lean_ctor_get(v_stx_920_, 1);
                        lean_inc(v_kind_963_);
                        v_args_964_ = lean_ctor_get(v_stx_920_, 2);
                        lean_inc_ref(v_args_964_);
                        lean_dec_ref_known(v_stx_920_, 3);
                        v___x_965_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1;
                        v___x_966_ = lean_name_eq(v_kind_963_, v___x_965_);
                        lean_dec(v_kind_963_);
                        if v___x_966_ == 0 {
                            v___y_934_ = v_args_964_;
                            v___y_935_ = v_a_961_;
                            state = 2;
                            continue;
                        } else {
                            v___x_967_ = lean_box(0);
                            v___x_968_ = lean_unsigned_to_nat(0);
                            v___x_969_ = lean_array_get(v___x_967_, v_args_964_, v___x_968_);
                            lean_dec_ref(v_args_964_);
                            v_stx_920_ = v___x_969_;
                            v_b_921_ = v_a_961_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stx_920_);
                    v_b_930_ = v_a_961_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v___x_972_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_920_);
                if v___x_972_ == 0 {
                    v_anti_973_ = l_Lean_Syntax_getAntiquotTerm(v_stx_920_);
                    v___x_974_ = l_Lean_Syntax_isIdent(v_anti_973_);
                    if v___x_974_ == 0 {
                        v___x_975_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4;
                        v___x_976_ = l_Lean_Syntax_isOfKind(v_anti_973_, v___x_975_);
                        if v___x_976_ == 0 {
                            v___x_977_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once), _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6);
                            v___x_978_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_920_, v___x_977_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
                            if lean_obj_tag(v___x_978_) == 0 {
                                lean_dec_ref_known(v___x_978_, 1);
                                v_a_961_ = v_b_921_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec_ref(v_b_921_);
                                lean_dec(v_stx_920_);
                                v_a_979_ = lean_ctor_get(v___x_978_, 0);
                                v_isSharedCheck_986_ = (!lean_is_exclusive(v___x_978_)) as u8;
                                if v_isSharedCheck_986_ == 0 {
                                    v___x_981_ = v___x_978_;
                                    v_isShared_982_ = v_isSharedCheck_986_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_979_);
                                    lean_dec(v___x_978_);
                                    v___x_981_ = lean_box(0);
                                    v_isShared_982_ = v_isSharedCheck_986_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            v_a_961_ = v_b_921_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_ids_987_ = lean_array_push(v_b_921_, v_anti_973_);
                        v_a_961_ = v_ids_987_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_961_ = v_b_921_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v_isShared_982_ == 0 {
                    v___x_984_ = v___x_981_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
                    v___x_984_ = v_reuseFailAlloc_985_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(
    mut v_firstChoiceOnly_990_: u8,
    mut v_as_991_: *mut LeanObject,
    mut v_sz_992_: usize,
    mut v_i_993_: usize,
    mut v_b_994_: *mut LeanObject,
    mut v___y_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1007_: u8 = 0;
    let mut v_a_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: usize = 0;
    let mut v___x_1026_: usize = 0;
    let mut v_reuseFailAlloc_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1029_: u8 = 0;
    let mut v_a_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1033_: u8 = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_isSharedCheck_1038_: u8 = 0;
    let mut v_unused_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1002_ = lean_usize_dec_lt(v_i_993_, v_sz_992_);
                if v___x_1002_ == 0 {
                    v___x_1003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1003_, 0, v_b_994_);
                    return v___x_1003_;
                } else {
                    v_snd_1004_ = lean_ctor_get(v_b_994_, 1);
                    v_isSharedCheck_1038_ = (!lean_is_exclusive(v_b_994_)) as u8;
                    if v_isSharedCheck_1038_ == 0 {
                        v_unused_1039_ = lean_ctor_get(v_b_994_, 0);
                        lean_dec(v_unused_1039_);
                        v___x_1006_ = v_b_994_;
                        v_isShared_1007_ = v_isSharedCheck_1038_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1004_);
                        lean_dec(v_b_994_);
                        v___x_1006_ = lean_box(0);
                        v_isShared_1007_ = v_isSharedCheck_1038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1008_ = lean_array_uget_borrowed(v_as_991_, v_i_993_);
                lean_inc(v_snd_1004_);
                lean_inc(v_a_1008_);
                v___x_1009_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_990_, v_a_1008_, v_snd_1004_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
                if lean_obj_tag(v___x_1009_) == 0 {
                    v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
                    v_isSharedCheck_1029_ = (!lean_is_exclusive(v___x_1009_)) as u8;
                    if v_isSharedCheck_1029_ == 0 {
                        v___x_1012_ = v___x_1009_;
                        v_isShared_1013_ = v_isSharedCheck_1029_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1010_);
                        lean_dec(v___x_1009_);
                        v___x_1012_ = lean_box(0);
                        v_isShared_1013_ = v_isSharedCheck_1029_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1006_);
                    lean_dec(v_snd_1004_);
                    v_a_1030_ = lean_ctor_get(v___x_1009_, 0);
                    v_isSharedCheck_1037_ = (!lean_is_exclusive(v___x_1009_)) as u8;
                    if v_isSharedCheck_1037_ == 0 {
                        v___x_1032_ = v___x_1009_;
                        v_isShared_1033_ = v_isSharedCheck_1037_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1030_);
                        lean_dec(v___x_1009_);
                        v___x_1032_ = lean_box(0);
                        v_isShared_1033_ = v_isSharedCheck_1037_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1010_) == 0 {
                    v___x_1014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1014_, 0, v_a_1010_);
                    if v_isShared_1007_ == 0 {
                        lean_ctor_set(v___x_1006_, 0, v___x_1014_);
                        v___x_1016_ = v___x_1006_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1014_);
                        lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_snd_1004_);
                        v___x_1016_ = v_reuseFailAlloc_1020_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1012_);
                    lean_dec(v_snd_1004_);
                    v_a_1021_ = lean_ctor_get(v_a_1010_, 0);
                    lean_inc(v_a_1021_);
                    lean_dec_ref_known(v_a_1010_, 1);
                    v___x_1022_ = lean_box(0);
                    if v_isShared_1007_ == 0 {
                        lean_ctor_set(v___x_1006_, 1, v_a_1021_);
                        lean_ctor_set(v___x_1006_, 0, v___x_1022_);
                        v___x_1024_ = v___x_1006_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1022_);
                        lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1021_);
                        v___x_1024_ = v_reuseFailAlloc_1028_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1013_ == 0 {
                    lean_ctor_set(v___x_1012_, 0, v___x_1016_);
                    v___x_1018_ = v___x_1012_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
                    v___x_1018_ = v_reuseFailAlloc_1019_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1018_;
            }
            5 => {
                v___x_1025_ = 1usize;
                v___x_1026_ = lean_usize_add(v_i_993_, v___x_1025_);
                v_i_993_ = v___x_1026_;
                v_b_994_ = v___x_1024_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1033_ == 0 {
                    v___x_1035_ = v___x_1032_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
                    v___x_1035_ = v_reuseFailAlloc_1036_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(
    mut v_firstChoiceOnly_1040_: *mut LeanObject,
    mut v_as_1041_: *mut LeanObject,
    mut v_sz_1042_: *mut LeanObject,
    mut v_i_1043_: *mut LeanObject,
    mut v_b_1044_: *mut LeanObject,
    mut v___y_1045_: *mut LeanObject,
    mut v___y_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
    mut v___y_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstChoiceOnly_boxed_1052_: u8 = 0;
    let mut v_sz_boxed_1053_: usize = 0;
    let mut v_i_boxed_1054_: usize = 0;
    let mut v_res_1055_: *mut LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_1052_ = (lean_unbox(v_firstChoiceOnly_1040_) as u8);
    v_sz_boxed_1053_ = lean_unbox_usize(v_sz_1042_);
    lean_dec(v_sz_1042_);
    v_i_boxed_1054_ = lean_unbox_usize(v_i_1043_);
    lean_dec(v_i_1043_);
    v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_boxed_1052_, v_as_1041_, v_sz_boxed_1053_, v_i_boxed_1054_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
    lean_dec(v___y_1050_);
    lean_dec_ref(v___y_1049_);
    lean_dec(v___y_1048_);
    lean_dec_ref(v___y_1047_);
    lean_dec(v___y_1046_);
    lean_dec_ref(v___y_1045_);
    lean_dec_ref(v_as_1041_);
    return v_res_1055_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(
    mut v_firstChoiceOnly_1056_: *mut LeanObject,
    mut v_stx_1057_: *mut LeanObject,
    mut v_b_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
    mut v___y_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
    mut v___y_1064_: *mut LeanObject,
    mut v___y_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstChoiceOnly_boxed_1066_: u8 = 0;
    let mut v_res_1067_: *mut LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_1066_ = (lean_unbox(v_firstChoiceOnly_1056_) as u8);
    v_res_1067_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_boxed_1066_, v_stx_1057_, v_b_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
    lean_dec(v___y_1064_);
    lean_dec_ref(v___y_1063_);
    lean_dec(v___y_1062_);
    lean_dec_ref(v___y_1061_);
    lean_dec(v___y_1060_);
    lean_dec_ref(v___y_1059_);
    return v_res_1067_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getAntiquotationIds(
    mut v_stx_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
    mut v_a_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_firstChoiceOnly_1080_: u8 = 0;
    let mut v_stx_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v_a_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1092_: u8 = 0;
    let mut v_a_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1096_: u8 = 0;
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1078_ = 1;
                v___x_1079_ = l_Lean_Syntax_topDown(v_stx_1070_, v___x_1078_);
                v_firstChoiceOnly_1080_ = lean_ctor_get_uint8(
                    v___x_1079_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_stx_1081_ = lean_ctor_get(v___x_1079_, 0);
                lean_inc(v_stx_1081_);
                lean_dec_ref(v___x_1079_);
                v_ids_1082_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0;
                v___x_1083_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_1080_, v_stx_1081_, v_ids_1082_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
                if lean_obj_tag(v___x_1083_) == 0 {
                    v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
                    v_isSharedCheck_1092_ = (!lean_is_exclusive(v___x_1083_)) as u8;
                    if v_isSharedCheck_1092_ == 0 {
                        v___x_1086_ = v___x_1083_;
                        v_isShared_1087_ = v_isSharedCheck_1092_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1084_);
                        lean_dec(v___x_1083_);
                        v___x_1086_ = lean_box(0);
                        v_isShared_1087_ = v_isSharedCheck_1092_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1093_ = lean_ctor_get(v___x_1083_, 0);
                    v_isSharedCheck_1100_ = (!lean_is_exclusive(v___x_1083_)) as u8;
                    if v_isSharedCheck_1100_ == 0 {
                        v___x_1095_ = v___x_1083_;
                        v_isShared_1096_ = v_isSharedCheck_1100_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1093_);
                        lean_dec(v___x_1083_);
                        v___x_1095_ = lean_box(0);
                        v_isShared_1096_ = v_isSharedCheck_1100_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1088_ = lean_ctor_get(v_a_1084_, 0);
                lean_inc(v_a_1088_);
                lean_dec(v_a_1084_);
                if v_isShared_1087_ == 0 {
                    lean_ctor_set(v___x_1086_, 0, v_a_1088_);
                    v___x_1090_ = v___x_1086_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1088_);
                    v___x_1090_ = v_reuseFailAlloc_1091_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1090_;
            }
            3 => {
                if v_isShared_1096_ == 0 {
                    v___x_1098_ = v___x_1095_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
                    v___x_1098_ = v_reuseFailAlloc_1099_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getAntiquotationIds___boxed(
    mut v_stx_1101_: *mut LeanObject,
    mut v_a_1102_: *mut LeanObject,
    mut v_a_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
    mut v_a_1105_: *mut LeanObject,
    mut v_a_1106_: *mut LeanObject,
    mut v_a_1107_: *mut LeanObject,
    mut v_a_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(
        v_stx_1101_,
        v_a_1102_,
        v_a_1103_,
        v_a_1104_,
        v_a_1105_,
        v_a_1106_,
        v_a_1107_,
    );
    lean_dec(v_a_1107_);
    lean_dec_ref(v_a_1106_);
    lean_dec(v_a_1105_);
    lean_dec_ref(v_a_1104_);
    lean_dec(v_a_1103_);
    lean_dec_ref(v_a_1102_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(
    mut v_00_u03b1_1110_: *mut LeanObject,
    mut v_ref_1111_: *mut LeanObject,
    mut v_msg_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
    mut v___y_1115_: *mut LeanObject,
    mut v___y_1116_: *mut LeanObject,
    mut v___y_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(
            v_ref_1111_,
            v_msg_1112_,
            v___y_1113_,
            v___y_1114_,
            v___y_1115_,
            v___y_1116_,
            v___y_1117_,
            v___y_1118_,
        );
    return v___x_1120_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___boxed(
    mut v_00_u03b1_1121_: *mut LeanObject,
    mut v_ref_1122_: *mut LeanObject,
    mut v_msg_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(
        v_00_u03b1_1121_,
        v_ref_1122_,
        v_msg_1123_,
        v___y_1124_,
        v___y_1125_,
        v___y_1126_,
        v___y_1127_,
        v___y_1128_,
        v___y_1129_,
    );
    lean_dec(v___y_1129_);
    lean_dec_ref(v___y_1128_);
    lean_dec(v___y_1127_);
    lean_dec_ref(v___y_1126_);
    lean_dec(v___y_1125_);
    lean_dec_ref(v___y_1124_);
    lean_dec(v_ref_1122_);
    return v_res_1131_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(
    mut v_00_u03b1_1132_: *mut LeanObject,
    mut v_msg_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    v___x_1141_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
    return v___x_1141_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___boxed(
    mut v_00_u03b1_1142_: *mut LeanObject,
    mut v_msg_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
    mut v___y_1149_: *mut LeanObject,
    mut v___y_1150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1151_: *mut LeanObject = core::ptr::null_mut();
    v_res_1151_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(v_00_u03b1_1142_, v_msg_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
    lean_dec(v___y_1149_);
    lean_dec_ref(v___y_1148_);
    lean_dec(v___y_1147_);
    lean_dec_ref(v___y_1146_);
    lean_dec(v___y_1145_);
    lean_dec_ref(v___y_1144_);
    return v_res_1151_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(
    mut v_msgData_1152_: *mut LeanObject,
    mut v_macroStack_1153_: *mut LeanObject,
    mut v___y_1154_: *mut LeanObject,
    mut v___y_1155_: *mut LeanObject,
    mut v___y_1156_: *mut LeanObject,
    mut v___y_1157_: *mut LeanObject,
    mut v___y_1158_: *mut LeanObject,
    mut v___y_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_1152_, v_macroStack_1153_, v___y_1158_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_1162_: *mut LeanObject,
    mut v_macroStack_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
    mut v___y_1165_: *mut LeanObject,
    mut v___y_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(v_msgData_1162_, v_macroStack_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
    lean_dec(v___y_1169_);
    lean_dec_ref(v___y_1168_);
    lean_dec(v___y_1167_);
    lean_dec_ref(v___y_1166_);
    lean_dec(v___y_1165_);
    lean_dec_ref(v___y_1164_);
    return v_res_1171_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5() -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lean_Elab_Term_Quotation_getPatternVars___closed__4;
    v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getPatternVars(
    mut v_stx_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: u8 = 0;
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: u8 = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1226_: u8 = 0;
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1242_: u8 = 0;
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut v_a_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1192_ = l_Lean_Syntax_isQuot(v_stx_1184_);
                if v___x_1192_ == 0 {
                    v___x_1193_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4;
                    lean_inc(v_stx_1184_);
                    v___x_1194_ = l_Lean_Syntax_isOfKind(v_stx_1184_, v___x_1193_);
                    if v___x_1194_ == 0 {
                        v___x_1195_ = l_Lean_Elab_Term_Quotation_getPatternVars___closed__1;
                        lean_inc(v_stx_1184_);
                        v___x_1196_ = l_Lean_Syntax_isOfKind(v_stx_1184_, v___x_1195_);
                        if v___x_1196_ == 0 {
                            v___x_1197_ = l_Lean_Elab_Term_Quotation_getPatternVars___closed__3;
                            lean_inc(v_stx_1184_);
                            v___x_1198_ = l_Lean_Syntax_isOfKind(v_stx_1184_, v___x_1197_);
                            if v___x_1198_ == 0 {
                                v___x_1199_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Term_Quotation_getPatternVars___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once
                                    ),
                                    _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5,
                                );
                                lean_inc(v_stx_1184_);
                                v___x_1200_ = l_Lean_MessageData_ofSyntax(v_stx_1184_);
                                v___x_1201_ = l_Lean_indentD(v___x_1200_);
                                v___x_1202_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1202_, 0, v___x_1199_);
                                lean_ctor_set(v___x_1202_, 1, v___x_1201_);
                                v___x_1203_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_1184_, v___x_1202_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
                                lean_dec(v_stx_1184_);
                                return v___x_1203_;
                            } else {
                                v___x_1204_ = lean_unsigned_to_nat(0);
                                v___x_1205_ = l_Lean_Syntax_getArg(v_stx_1184_, v___x_1204_);
                                lean_inc(v___x_1205_);
                                v___x_1206_ = l_Lean_Syntax_isOfKind(v___x_1205_, v___x_1195_);
                                if v___x_1206_ == 0 {
                                    lean_dec(v___x_1205_);
                                    v___x_1207_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once), _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
                                    lean_inc(v_stx_1184_);
                                    v___x_1208_ = l_Lean_MessageData_ofSyntax(v_stx_1184_);
                                    v___x_1209_ = l_Lean_indentD(v___x_1208_);
                                    v___x_1210_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_1210_, 0, v___x_1207_);
                                    lean_ctor_set(v___x_1210_, 1, v___x_1209_);
                                    v___x_1211_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_1184_, v___x_1210_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
                                    lean_dec(v_stx_1184_);
                                    return v___x_1211_;
                                } else {
                                    v___x_1212_ = lean_unsigned_to_nat(2);
                                    v___x_1213_ = l_Lean_Syntax_getArg(v_stx_1184_, v___x_1212_);
                                    v___x_1214_ =
                                        l_Lean_Syntax_matchesNull(v___x_1213_, v___x_1204_);
                                    if v___x_1214_ == 0 {
                                        lean_dec(v___x_1205_);
                                        v___x_1215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once), _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
                                        lean_inc(v_stx_1184_);
                                        v___x_1216_ = l_Lean_MessageData_ofSyntax(v_stx_1184_);
                                        v___x_1217_ = l_Lean_indentD(v___x_1216_);
                                        v___x_1218_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_1218_, 0, v___x_1215_);
                                        lean_ctor_set(v___x_1218_, 1, v___x_1217_);
                                        v___x_1219_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_1184_, v___x_1218_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
                                        lean_dec(v_stx_1184_);
                                        return v___x_1219_;
                                    } else {
                                        v___x_1220_ = lean_unsigned_to_nat(3);
                                        v___x_1221_ =
                                            l_Lean_Syntax_getArg(v_stx_1184_, v___x_1220_);
                                        lean_dec(v_stx_1184_);
                                        v___x_1222_ = l_Lean_Elab_Term_Quotation_getPatternVars(
                                            v___x_1221_,
                                            v_a_1185_,
                                            v_a_1186_,
                                            v_a_1187_,
                                            v_a_1188_,
                                            v_a_1189_,
                                            v_a_1190_,
                                        );
                                        if lean_obj_tag(v___x_1222_) == 0 {
                                            v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
                                            v_isSharedCheck_1231_ =
                                                (!lean_is_exclusive(v___x_1222_)) as u8;
                                            if v_isSharedCheck_1231_ == 0 {
                                                v___x_1225_ = v___x_1222_;
                                                v_isShared_1226_ = v_isSharedCheck_1231_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1223_);
                                                lean_dec(v___x_1222_);
                                                v___x_1225_ = lean_box(0);
                                                v_isShared_1226_ = v_isSharedCheck_1231_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_1205_);
                                            return v___x_1222_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_1232_ = lean_unsigned_to_nat(1);
                            v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1232_);
                            v___x_1234_ = lean_array_push(v___x_1233_, v_stx_1184_);
                            v___x_1235_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1235_, 0, v___x_1234_);
                            return v___x_1235_;
                        }
                    } else {
                        lean_dec(v_stx_1184_);
                        v___x_1236_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0;
                        v___x_1237_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1237_, 0, v___x_1236_);
                        return v___x_1237_;
                    }
                } else {
                    v___x_1238_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(
                        v_stx_1184_,
                        v_a_1185_,
                        v_a_1186_,
                        v_a_1187_,
                        v_a_1188_,
                        v_a_1189_,
                        v_a_1190_,
                    );
                    if lean_obj_tag(v___x_1238_) == 0 {
                        v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
                        v_isSharedCheck_1246_ = (!lean_is_exclusive(v___x_1238_)) as u8;
                        if v_isSharedCheck_1246_ == 0 {
                            v___x_1241_ = v___x_1238_;
                            v_isShared_1242_ = v_isSharedCheck_1246_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1239_);
                            lean_dec(v___x_1238_);
                            v___x_1241_ = lean_box(0);
                            v_isShared_1242_ = v_isSharedCheck_1246_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1247_ = lean_ctor_get(v___x_1238_, 0);
                        v_isSharedCheck_1254_ = (!lean_is_exclusive(v___x_1238_)) as u8;
                        if v_isSharedCheck_1254_ == 0 {
                            v___x_1249_ = v___x_1238_;
                            v_isShared_1250_ = v_isSharedCheck_1254_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1247_);
                            lean_dec(v___x_1238_);
                            v___x_1249_ = lean_box(0);
                            v_isShared_1250_ = v_isSharedCheck_1254_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1227_ = lean_array_push(v_a_1223_, v___x_1205_);
                if v_isShared_1226_ == 0 {
                    lean_ctor_set(v___x_1225_, 0, v___x_1227_);
                    v___x_1229_ = v___x_1225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
                    v___x_1229_ = v_reuseFailAlloc_1230_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1229_;
            }
            3 => {
                if v_isShared_1242_ == 0 {
                    v___x_1244_ = v___x_1241_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
                    v___x_1244_ = v_reuseFailAlloc_1245_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1244_;
            }
            5 => {
                if v_isShared_1250_ == 0 {
                    v___x_1252_ = v___x_1249_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
                    v___x_1252_ = v_reuseFailAlloc_1253_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getPatternVars___boxed(
    mut v_stx_1255_: *mut LeanObject,
    mut v_a_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1263_: *mut LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lean_Elab_Term_Quotation_getPatternVars(
        v_stx_1255_,
        v_a_1256_,
        v_a_1257_,
        v_a_1258_,
        v_a_1259_,
        v_a_1260_,
        v_a_1261_,
    );
    lean_dec(v_a_1261_);
    lean_dec_ref(v_a_1260_);
    lean_dec(v_a_1259_);
    lean_dec_ref(v_a_1258_);
    lean_dec(v_a_1257_);
    lean_dec_ref(v_a_1256_);
    return v_res_1263_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(
    mut v_as_1264_: *mut LeanObject,
    mut v_i_1265_: usize,
    mut v_stop_1266_: usize,
    mut v_b_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: usize = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1280_: u8 = 0;
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1280_ = lean_usize_dec_eq(v_i_1265_, v_stop_1266_);
                if v___x_1280_ == 0 {
                    v___x_1281_ = lean_array_uget_borrowed(v_as_1264_, v_i_1265_);
                    lean_inc(v___x_1281_);
                    v___x_1282_ = l_Lean_Elab_Term_Quotation_getPatternVars(
                        v___x_1281_,
                        v___y_1268_,
                        v___y_1269_,
                        v___y_1270_,
                        v___y_1271_,
                        v___y_1272_,
                        v___y_1273_,
                    );
                    if lean_obj_tag(v___x_1282_) == 0 {
                        v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
                        lean_inc(v_a_1283_);
                        lean_dec_ref_known(v___x_1282_, 1);
                        v___x_1284_ = l_Array_append___redArg(v_b_1267_, v_a_1283_);
                        lean_dec(v_a_1283_);
                        v_a_1276_ = v___x_1284_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_1267_);
                        if lean_obj_tag(v___x_1282_) == 0 {
                            v_a_1285_ = lean_ctor_get(v___x_1282_, 0);
                            lean_inc(v_a_1285_);
                            lean_dec_ref_known(v___x_1282_, 1);
                            v_a_1276_ = v_a_1285_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_1282_;
                        }
                    }
                } else {
                    v___x_1286_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1286_, 0, v_b_1267_);
                    return v___x_1286_;
                }
            }
            1 => {
                v___x_1277_ = 1usize;
                v___x_1278_ = lean_usize_add(v_i_1265_, v___x_1277_);
                v_i_1265_ = v___x_1278_;
                v_b_1267_ = v_a_1276_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0___boxed(
    mut v_as_1287_: *mut LeanObject,
    mut v_i_1288_: *mut LeanObject,
    mut v_stop_1289_: *mut LeanObject,
    mut v_b_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1298_: usize = 0;
    let mut v_stop_boxed_1299_: usize = 0;
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1298_ = lean_unbox_usize(v_i_1288_);
    lean_dec(v_i_1288_);
    v_stop_boxed_1299_ = lean_unbox_usize(v_stop_1289_);
    lean_dec(v_stop_1289_);
    v_res_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_as_1287_, v_i_boxed_1298_, v_stop_boxed_1299_, v_b_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
    lean_dec(v___y_1296_);
    lean_dec_ref(v___y_1295_);
    lean_dec(v___y_1294_);
    lean_dec_ref(v___y_1293_);
    lean_dec(v___y_1292_);
    lean_dec_ref(v___y_1291_);
    lean_dec_ref(v_as_1287_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getPatternsVars(
    mut v_pats_1301_: *mut LeanObject,
    mut v_a_1302_: *mut LeanObject,
    mut v_a_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_a_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    v___x_1309_ = lean_unsigned_to_nat(0);
    v___x_1310_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0;
    v___x_1311_ = lean_array_get_size(v_pats_1301_);
    v___x_1312_ = lean_nat_dec_lt(v___x_1309_, v___x_1311_);
    if v___x_1312_ == 0 {
        let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
        v___x_1313_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1313_, 0, v___x_1310_);
        return v___x_1313_;
    } else {
        let mut v___x_1314_: u8 = 0;
        v___x_1314_ = lean_nat_dec_le(v___x_1311_, v___x_1311_);
        if v___x_1314_ == 0 {
            if v___x_1312_ == 0 {
                let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
                v___x_1315_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1315_, 0, v___x_1310_);
                return v___x_1315_;
            } else {
                let mut v___x_1316_: usize = 0;
                let mut v___x_1317_: usize = 0;
                let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
                v___x_1316_ = 0usize;
                v___x_1317_ = lean_usize_of_nat(v___x_1311_);
                v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_1301_, v___x_1316_, v___x_1317_, v___x_1310_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
                return v___x_1318_;
            }
        } else {
            let mut v___x_1319_: usize = 0;
            let mut v___x_1320_: usize = 0;
            let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
            v___x_1319_ = 0usize;
            v___x_1320_ = lean_usize_of_nat(v___x_1311_);
            v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_1301_, v___x_1319_, v___x_1320_, v___x_1310_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
            return v___x_1321_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getPatternsVars___boxed(
    mut v_pats_1322_: *mut LeanObject,
    mut v_a_1323_: *mut LeanObject,
    mut v_a_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
    mut v_a_1328_: *mut LeanObject,
    mut v_a_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_Elab_Term_Quotation_getPatternsVars(
        v_pats_1322_,
        v_a_1323_,
        v_a_1324_,
        v_a_1325_,
        v_a_1326_,
        v_a_1327_,
        v_a_1328_,
    );
    lean_dec(v_a_1328_);
    lean_dec_ref(v_a_1327_);
    lean_dec(v_a_1326_);
    lean_dec_ref(v_a_1325_);
    lean_dec(v_a_1324_);
    lean_dec_ref(v_a_1323_);
    lean_dec_ref(v_pats_1322_);
    return v_res_1330_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(
    mut v_antiquot_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    v___x_1332_ = lean_unsigned_to_nat(3);
    v___x_1333_ = l_Lean_Syntax_getArg(v_antiquot_1331_, v___x_1332_);
    v___x_1334_ = lean_unsigned_to_nat(1);
    v_name_1335_ = l_Lean_Syntax_getArg(v___x_1333_, v___x_1334_);
    lean_dec(v___x_1333_);
    v___x_1336_ = l_Lean_Syntax_isMissing(v_name_1335_);
    if v___x_1336_ == 0 {
        let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
        v___x_1337_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1337_, 0, v_name_1335_);
        return v___x_1337_;
    } else {
        let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_name_1335_);
        v___x_1338_ = lean_box(0);
        return v___x_1338_;
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f___boxed(
    mut v_antiquot_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(v_antiquot_1339_);
    lean_dec(v_antiquot_1339_);
    return v_res_1340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Quotation_Util(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Term_Quotation_hygiene = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_Term_Quotation_hygiene);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Quotation_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Quotation_Util(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Elab_Quotation_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Quotation_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Quotation_Util(builtin);
}
