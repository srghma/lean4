// Lean compiler output
// Module: Lean.Elab.BuiltinDo.TryCatch
// Imports: Lean.Elab.Do.Basic Lean.Parser.Do Lean.Elab.Do.Control
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_mkHole};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node5,
    l_Lean_Syntax_node7, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Elab::Binders::l_Lean_Elab_Term_elabBinder___redArg;
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure,
    l_Lean_Elab_Do_DoElemCont_mkPure___redArg, l_Lean_Elab_Do_checkMutVarsForShadowing,
    l_Lean_Elab_Do_doElemElabAttribute, l_Lean_Elab_Do_elabDoSeq, l_Lean_Elab_Do_elabDoSeq___boxed,
    l_Lean_Elab_Do_enterFinally, l_Lean_Elab_Do_mkFreshResultType___redArg,
    runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Do::Control::{
    initialize_Lean_Elab_Do_Control, l_Lean_Elab_Do_ControlLifter_lift,
    l_Lean_Elab_Do_ControlLifter_ofCont, l_Lean_Elab_Do_ControlLifter_restoreCont,
    runtime_initialize_Lean_Elab_Do_Control,
};
use crate::r#gen::Lean::Elab::Do::InferControlInfo::l_Lean_Elab_Do_inferControlInfoElem;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_mkExplicitBinder, l_Lean_Elab_Term_mkInstMVar,
    l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_mvarId_x21, l_Lean_mkApp6, l_Lean_mkApp7,
    l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_mkLambdaFVars;
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_getDecLevel;
use crate::r#gen::Lean::Parser::Do::{initialize_Lean_Parser_Do, meta_initialize_Lean_Parser_Do};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [77, 111, 110, 97, 100, 69, 120, 99, 101, 112, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value) as *mut LeanObject,8171668748642392738 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 114, 121, 67, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value) as *mut LeanObject,8171668748642392738 as *mut LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2_value) as *mut LeanObject,9442893686410543527 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [77, 111, 110, 97, 100, 69, 120, 99, 101, 112, 116, 79, 102, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4_value) as *mut LeanObject,18207456035884958142 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 114, 121, 67, 97, 116, 99, 104, 84, 104, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6_value) as *mut LeanObject,7054863150932804130 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 67, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3_value
) as *mut LeanObject;
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3_value) as *mut LeanObject,582343481276482584 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 111, 67, 97, 116, 99, 104, 77, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value) as *mut LeanObject,2212687648404433478 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 77, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14_value) as *mut LeanObject,4365236509002904093 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17_value) as *mut LeanObject,9383794970646754147 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [100, 111, 84, 114, 121, 0],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Do_elabDoTry___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__0_value) as *mut LeanObject,
        14629134714403383735 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 1,
    m_data: [206, 178, 0],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__2_value) as *mut LeanObject,
        17935790504110801827 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__4_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [77, 111, 110, 97, 100, 70, 105, 110, 97, 108, 108, 121, 0],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__4_value) as *mut LeanObject,
        11963028271846728275 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__6_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [70, 117, 110, 99, 116, 111, 114, 0],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__6_value) as *mut LeanObject,
        2226500928782199335 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__8_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 114, 121, 70, 105, 110, 97, 108, 108, 121, 0],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__8_value) as *mut LeanObject,
        5705947774479117410 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoTry___closed__10_value: LeanStringObject<53> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 96, 116, 114, 121, 96, 46, 32, 84, 104, 101, 114, 101,
        32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 32, 96, 99, 97, 116, 99, 104, 96, 32, 111,
        114, 32, 96, 102, 105, 110, 97, 108, 108, 121, 96, 46, 0,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__10_value) as *mut LeanObject;
static mut l_Lean_Elab_Do_elabDoTry___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_elabDoTry___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoTry___closed__12_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 111, 70, 105, 110, 97, 108, 108, 121, 0],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__12_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Do_elabDoTry___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__12_value) as *mut LeanObject,
        16078196552099809630 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoTry___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoTry___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 68, 111, 84, 114, 121, 0]};
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1_value) as *mut LeanObject,102172329646148436 as *mut LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2_value) as *mut LeanObject,16702866075349626691 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_797_ = lean_box(0);
    v___x_798_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_799_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_799_, 0, v___x_798_);
    lean_ctor_set(v___x_799_, 1, v___x_797_);
    return v___x_799_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v___x_801_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0);
    v___x_802_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_802_, 0, v___x_801_);
    return v___x_802_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___boxed(
    mut v___y_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
    return v_res_804_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(
    mut v_00_u03b1_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
    mut v___y_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
    return v___x_814_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___boxed(
    mut v_00_u03b1_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
    mut v___y_817_: *mut LeanObject,
    mut v___y_818_: *mut LeanObject,
    mut v___y_819_: *mut LeanObject,
    mut v___y_820_: *mut LeanObject,
    mut v___y_821_: *mut LeanObject,
    mut v___y_822_: *mut LeanObject,
    mut v___y_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_824_: *mut LeanObject = core::ptr::null_mut();
    v_res_824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(v_00_u03b1_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
    lean_dec(v___y_822_);
    lean_dec_ref(v___y_821_);
    lean_dec(v___y_820_);
    lean_dec_ref(v___y_819_);
    lean_dec(v___y_818_);
    lean_dec_ref(v___y_817_);
    lean_dec_ref(v___y_816_);
    return v_res_824_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(
    mut v___x_825_: *mut LeanObject,
    mut v___x_826_: u8,
    mut v_cont_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
    mut v___y_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
    mut v___y_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Elab_Do_elabDoSeq(
        v___x_825_,
        v_cont_827_,
        v___x_826_,
        v___y_828_,
        v___y_829_,
        v___y_830_,
        v___y_831_,
        v___y_832_,
        v___y_833_,
        v___y_834_,
    );
    return v___x_836_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed(
    mut v___x_837_: *mut LeanObject,
    mut v___x_838_: *mut LeanObject,
    mut v_cont_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
    mut v___y_844_: *mut LeanObject,
    mut v___y_845_: *mut LeanObject,
    mut v___y_846_: *mut LeanObject,
    mut v___y_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4680__boxed_848_: u8 = 0;
    let mut v_res_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_4680__boxed_848_ = (lean_unbox(v___x_838_) as u8);
    v_res_849_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(
        v___x_837_,
        v___x_4680__boxed_848_,
        v_cont_839_,
        v___y_840_,
        v___y_841_,
        v___y_842_,
        v___y_843_,
        v___y_844_,
        v___y_845_,
        v___y_846_,
    );
    lean_dec(v___y_846_);
    lean_dec_ref(v___y_845_);
    lean_dec(v___y_844_);
    lean_dec_ref(v___y_843_);
    lean_dec(v___y_842_);
    lean_dec_ref(v___y_841_);
    lean_dec_ref(v___y_840_);
    return v_res_849_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(
    mut v_lifter_863_: *mut LeanObject,
    mut v___f_864_: *mut LeanObject,
    mut v___x_865_: *mut LeanObject,
    mut v___x_866_: u8,
    mut v_monadInfo_867_: *mut LeanObject,
    mut v_body_868_: *mut LeanObject,
    mut v___y_869_: *mut LeanObject,
    mut v_eType_x3f_870_: *mut LeanObject,
    mut v_x_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_catcher_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: u8 = 0;
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_liftedDoBlockResultType_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_liftedDoBlockResultType_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_877_);
                lean_inc_ref(v___y_876_);
                lean_inc(v___y_875_);
                lean_inc_ref(v___y_874_);
                lean_inc_ref(v_x_871_);
                v___x_904_ =
                    lean_infer_type(v_x_871_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
                if lean_obj_tag(v___x_904_) == 0 {
                    v_a_905_ = lean_ctor_get(v___x_904_, 0);
                    lean_inc_n(v_a_905_, 2);
                    lean_dec_ref_known(v___x_904_, 1);
                    v___x_906_ = l_Lean_Meta_getDecLevel(
                        v_a_905_, v___y_874_, v___y_875_, v___y_876_, v___y_877_,
                    );
                    if lean_obj_tag(v___x_906_) == 0 {
                        v_a_907_ = lean_ctor_get(v___x_906_, 0);
                        lean_inc(v_a_907_);
                        lean_dec_ref_known(v___x_906_, 1);
                        if lean_obj_tag(v_eType_x3f_870_) == 0 {
                            state = 4;
                            continue;
                        } else {
                            if v___x_866_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v_m_926_ = lean_ctor_get(v_monadInfo_867_, 0);
                                lean_inc_ref_n(v_m_926_, 2);
                                v_u_927_ = lean_ctor_get(v_monadInfo_867_, 1);
                                lean_inc(v_u_927_);
                                v_v_928_ = lean_ctor_get(v_monadInfo_867_, 2);
                                lean_inc(v_v_928_);
                                lean_dec_ref(v_monadInfo_867_);
                                v___x_929_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5;
                                v___x_930_ = lean_box(0);
                                v___x_931_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_931_, 0, v_v_928_);
                                lean_ctor_set(v___x_931_, 1, v___x_930_);
                                v___x_932_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_932_, 0, v_u_927_);
                                lean_ctor_set(v___x_932_, 1, v___x_931_);
                                v___x_933_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_933_, 0, v_a_907_);
                                lean_ctor_set(v___x_933_, 1, v___x_932_);
                                lean_inc_ref(v___x_933_);
                                v___x_934_ = l_Lean_mkConst(v___x_929_, v___x_933_);
                                lean_inc(v_a_905_);
                                v___x_935_ = l_Lean_mkAppB(v___x_934_, v_a_905_, v_m_926_);
                                v___x_936_ = lean_box(0);
                                v___x_937_ = l_Lean_Elab_Term_mkInstMVar(
                                    v___x_935_, v___x_936_, v___y_872_, v___y_873_, v___y_874_,
                                    v___y_875_, v___y_876_, v___y_877_,
                                );
                                if lean_obj_tag(v___x_937_) == 0 {
                                    v_a_938_ = lean_ctor_get(v___x_937_, 0);
                                    lean_inc(v_a_938_);
                                    lean_dec_ref_known(v___x_937_, 1);
                                    v_liftedDoBlockResultType_939_ =
                                        lean_ctor_get(v_lifter_863_, 5);
                                    v___x_940_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7;
                                    v___x_941_ = l_Lean_mkConst(v___x_940_, v___x_933_);
                                    lean_inc_ref(v_liftedDoBlockResultType_939_);
                                    v___x_942_ = lean_alloc_closure(
                                        l_Lean_mkApp6 as *mut core::ffi::c_void,
                                        7,
                                        6,
                                    );
                                    lean_closure_set(v___x_942_, 0, v___x_941_);
                                    lean_closure_set(v___x_942_, 1, v_a_905_);
                                    lean_closure_set(v___x_942_, 2, v_m_926_);
                                    lean_closure_set(v___x_942_, 3, v_a_938_);
                                    lean_closure_set(v___x_942_, 4, v_liftedDoBlockResultType_939_);
                                    lean_closure_set(v___x_942_, 5, v_body_868_);
                                    v_catcher_880_ = v___x_942_;
                                    v___y_881_ = v___y_869_;
                                    v___y_882_ = v___y_872_;
                                    v___y_883_ = v___y_873_;
                                    v___y_884_ = v___y_874_;
                                    v___y_885_ = v___y_875_;
                                    v___y_886_ = v___y_876_;
                                    v___y_887_ = v___y_877_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___x_933_, 2);
                                    lean_dec_ref(v_m_926_);
                                    lean_dec(v_a_905_);
                                    lean_dec_ref(v_x_871_);
                                    lean_dec_ref(v_body_868_);
                                    lean_dec_ref(v___f_864_);
                                    lean_dec_ref(v_lifter_863_);
                                    return v___x_937_;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_905_);
                        lean_dec_ref(v_x_871_);
                        lean_dec_ref(v_body_868_);
                        lean_dec_ref(v_monadInfo_867_);
                        lean_dec_ref(v___f_864_);
                        lean_dec_ref(v_lifter_863_);
                        v_a_943_ = lean_ctor_get(v___x_906_, 0);
                        v_isSharedCheck_950_ = (!lean_is_exclusive(v___x_906_)) as u8;
                        if v_isSharedCheck_950_ == 0 {
                            v___x_945_ = v___x_906_;
                            v_isShared_946_ = v_isSharedCheck_950_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_943_);
                            lean_dec(v___x_906_);
                            v___x_945_ = lean_box(0);
                            v_isShared_946_ = v_isSharedCheck_950_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_871_);
                    lean_dec_ref(v_body_868_);
                    lean_dec_ref(v_monadInfo_867_);
                    lean_dec_ref(v___f_864_);
                    lean_dec_ref(v_lifter_863_);
                    return v___x_904_;
                }
            }
            1 => {
                v___x_888_ = l_Lean_Elab_Do_ControlLifter_lift(
                    v_lifter_863_,
                    v___f_864_,
                    v___y_881_,
                    v___y_882_,
                    v___y_883_,
                    v___y_884_,
                    v___y_885_,
                    v___y_886_,
                    v___y_887_,
                );
                if lean_obj_tag(v___x_888_) == 0 {
                    v_a_889_ = lean_ctor_get(v___x_888_, 0);
                    lean_inc(v_a_889_);
                    lean_dec_ref_known(v___x_888_, 1);
                    v___x_890_ = lean_mk_empty_array_with_capacity(v___x_865_);
                    v___x_891_ = lean_array_push(v___x_890_, v_x_871_);
                    v___x_892_ = 0;
                    v___x_893_ = 1;
                    v___x_894_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_891_, v_a_889_, v___x_892_, v___x_866_, v___x_892_, v___x_866_,
                        v___x_893_, v___y_884_, v___y_885_, v___y_886_, v___y_887_,
                    );
                    lean_dec_ref(v___x_891_);
                    if lean_obj_tag(v___x_894_) == 0 {
                        v_a_895_ = lean_ctor_get(v___x_894_, 0);
                        v_isSharedCheck_903_ = (!lean_is_exclusive(v___x_894_)) as u8;
                        if v_isSharedCheck_903_ == 0 {
                            v___x_897_ = v___x_894_;
                            v_isShared_898_ = v_isSharedCheck_903_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_895_);
                            lean_dec(v___x_894_);
                            v___x_897_ = lean_box(0);
                            v_isShared_898_ = v_isSharedCheck_903_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_catcher_880_);
                        return v___x_894_;
                    }
                } else {
                    lean_dec_ref(v_catcher_880_);
                    lean_dec_ref(v_x_871_);
                    return v___x_888_;
                }
            }
            2 => {
                v___x_899_ = lean_apply_1(v_catcher_880_, v_a_895_);
                if v_isShared_898_ == 0 {
                    lean_ctor_set(v___x_897_, 0, v___x_899_);
                    v___x_901_ = v___x_897_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
                    v___x_901_ = v_reuseFailAlloc_902_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_901_;
            }
            4 => {
                v_m_909_ = lean_ctor_get(v_monadInfo_867_, 0);
                lean_inc_ref_n(v_m_909_, 2);
                v_u_910_ = lean_ctor_get(v_monadInfo_867_, 1);
                lean_inc(v_u_910_);
                v_v_911_ = lean_ctor_get(v_monadInfo_867_, 2);
                lean_inc(v_v_911_);
                lean_dec_ref(v_monadInfo_867_);
                v___x_912_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1;
                v___x_913_ = lean_box(0);
                v___x_914_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_914_, 0, v_v_911_);
                lean_ctor_set(v___x_914_, 1, v___x_913_);
                v___x_915_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_915_, 0, v_u_910_);
                lean_ctor_set(v___x_915_, 1, v___x_914_);
                v___x_916_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_916_, 0, v_a_907_);
                lean_ctor_set(v___x_916_, 1, v___x_915_);
                lean_inc_ref(v___x_916_);
                v___x_917_ = l_Lean_mkConst(v___x_912_, v___x_916_);
                lean_inc(v_a_905_);
                v___x_918_ = l_Lean_mkAppB(v___x_917_, v_a_905_, v_m_909_);
                v___x_919_ = lean_box(0);
                v___x_920_ = l_Lean_Elab_Term_mkInstMVar(
                    v___x_918_, v___x_919_, v___y_872_, v___y_873_, v___y_874_, v___y_875_,
                    v___y_876_, v___y_877_,
                );
                if lean_obj_tag(v___x_920_) == 0 {
                    v_a_921_ = lean_ctor_get(v___x_920_, 0);
                    lean_inc(v_a_921_);
                    lean_dec_ref_known(v___x_920_, 1);
                    v_liftedDoBlockResultType_922_ = lean_ctor_get(v_lifter_863_, 5);
                    v___x_923_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3;
                    v___x_924_ = l_Lean_mkConst(v___x_923_, v___x_916_);
                    lean_inc_ref(v_liftedDoBlockResultType_922_);
                    v___x_925_ = lean_alloc_closure(l_Lean_mkApp6 as *mut core::ffi::c_void, 7, 6);
                    lean_closure_set(v___x_925_, 0, v___x_924_);
                    lean_closure_set(v___x_925_, 1, v_a_905_);
                    lean_closure_set(v___x_925_, 2, v_m_909_);
                    lean_closure_set(v___x_925_, 3, v_a_921_);
                    lean_closure_set(v___x_925_, 4, v_liftedDoBlockResultType_922_);
                    lean_closure_set(v___x_925_, 5, v_body_868_);
                    v_catcher_880_ = v___x_925_;
                    v___y_881_ = v___y_869_;
                    v___y_882_ = v___y_872_;
                    v___y_883_ = v___y_873_;
                    v___y_884_ = v___y_874_;
                    v___y_885_ = v___y_875_;
                    v___y_886_ = v___y_876_;
                    v___y_887_ = v___y_877_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_916_, 2);
                    lean_dec_ref(v_m_909_);
                    lean_dec(v_a_905_);
                    lean_dec_ref(v_x_871_);
                    lean_dec_ref(v_body_868_);
                    lean_dec_ref(v___f_864_);
                    lean_dec_ref(v_lifter_863_);
                    return v___x_920_;
                }
            }
            5 => {
                if v_isShared_946_ == 0 {
                    v___x_948_ = v___x_945_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
                    v___x_948_ = v_reuseFailAlloc_949_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed(
    mut v_lifter_951_: *mut LeanObject,
    mut v___f_952_: *mut LeanObject,
    mut v___x_953_: *mut LeanObject,
    mut v___x_954_: *mut LeanObject,
    mut v_monadInfo_955_: *mut LeanObject,
    mut v_body_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
    mut v_eType_x3f_958_: *mut LeanObject,
    mut v_x_959_: *mut LeanObject,
    mut v___y_960_: *mut LeanObject,
    mut v___y_961_: *mut LeanObject,
    mut v___y_962_: *mut LeanObject,
    mut v___y_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
    mut v___y_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4739__boxed_967_: u8 = 0;
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v___x_4739__boxed_967_ = (lean_unbox(v___x_954_) as u8);
    v_res_968_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(
        v_lifter_951_,
        v___f_952_,
        v___x_953_,
        v___x_4739__boxed_967_,
        v_monadInfo_955_,
        v_body_956_,
        v___y_957_,
        v_eType_x3f_958_,
        v_x_959_,
        v___y_960_,
        v___y_961_,
        v___y_962_,
        v___y_963_,
        v___y_964_,
        v___y_965_,
    );
    lean_dec(v___y_965_);
    lean_dec_ref(v___y_964_);
    lean_dec(v___y_963_);
    lean_dec_ref(v___y_962_);
    lean_dec(v___y_961_);
    lean_dec_ref(v___y_960_);
    lean_dec(v_eType_x3f_958_);
    lean_dec_ref(v___y_957_);
    lean_dec(v___x_953_);
    return v_res_968_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(
    mut v_lifter_978_: *mut LeanObject,
    mut v_body_979_: *mut LeanObject,
    mut v_catch___980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
    mut v_a_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
    mut v_a_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eType_x3f_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_989_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4;
                lean_inc(v_catch___980_);
                v___x_990_ = l_Lean_Syntax_isOfKind(v_catch___980_, v___x_989_);
                if v___x_990_ == 0 {
                    lean_dec(v_catch___980_);
                    lean_dec_ref(v_body_979_);
                    lean_dec_ref(v_lifter_978_);
                    v___x_991_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
                    return v___x_991_;
                } else {
                    v_monadInfo_992_ = lean_ctor_get(v_a_981_, 0);
                    v___x_993_ = lean_unsigned_to_nat(1);
                    v___x_994_ = l_Lean_Syntax_getArg(v_catch___980_, v___x_993_);
                    v___x_1024_ = lean_unsigned_to_nat(2);
                    v___x_1025_ = l_Lean_Syntax_getArg(v_catch___980_, v___x_1024_);
                    v___x_1026_ = l_Lean_Syntax_isNone(v___x_1025_);
                    if v___x_1026_ == 0 {
                        lean_inc(v___x_1025_);
                        v___x_1027_ = l_Lean_Syntax_matchesNull(v___x_1025_, v___x_1024_);
                        if v___x_1027_ == 0 {
                            lean_dec(v___x_1025_);
                            lean_dec(v___x_994_);
                            lean_dec(v_catch___980_);
                            lean_dec_ref(v_body_979_);
                            lean_dec_ref(v_lifter_978_);
                            v___x_1028_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
                            return v___x_1028_;
                        } else {
                            v___x_1029_ = l_Lean_Syntax_getArg(v___x_1025_, v___x_993_);
                            lean_dec(v___x_1025_);
                            v___x_1030_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1030_, 0, v___x_1029_);
                            v_eType_x3f_1007_ = v___x_1030_;
                            v___y_1008_ = v_a_981_;
                            v___y_1009_ = v_a_982_;
                            v___y_1010_ = v_a_983_;
                            v___y_1011_ = v_a_984_;
                            v___y_1012_ = v_a_985_;
                            v___y_1013_ = v_a_986_;
                            v___y_1014_ = v_a_987_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1025_);
                        v___x_1031_ = lean_box(0);
                        v_eType_x3f_1007_ = v___x_1031_;
                        v___y_1008_ = v_a_981_;
                        v___y_1009_ = v_a_982_;
                        v___y_1010_ = v_a_983_;
                        v___y_1011_ = v_a_984_;
                        v___y_1012_ = v_a_985_;
                        v___y_1013_ = v_a_986_;
                        v___y_1014_ = v_a_987_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1004_ = l_Lean_Elab_Term_mkExplicitBinder(v___x_994_, v___y_1003_);
                v___x_1005_ = l_Lean_Elab_Term_elabBinder___redArg(
                    v___x_1004_,
                    v___y_998_,
                    v___y_999_,
                    v___y_1001_,
                    v___y_1002_,
                    v___y_997_,
                    v___y_1000_,
                    v___y_996_,
                );
                return v___x_1005_;
            }
            2 => {
                v___x_1015_ = lean_unsigned_to_nat(4);
                v___x_1016_ = l_Lean_Syntax_getArg(v_catch___980_, v___x_1015_);
                lean_dec(v_catch___980_);
                v___x_1017_ = lean_box((v___x_990_) as usize);
                v___f_1018_ = lean_alloc_closure(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                lean_closure_set(v___f_1018_, 0, v___x_1016_);
                lean_closure_set(v___f_1018_, 1, v___x_1017_);
                v___x_1019_ = lean_box((v___x_990_) as usize);
                lean_inc(v_eType_x3f_1007_);
                lean_inc_ref(v___y_1008_);
                lean_inc_ref(v_monadInfo_992_);
                v___f_1020_ = lean_alloc_closure(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed as *mut core::ffi::c_void, 16, 8);
                lean_closure_set(v___f_1020_, 0, v_lifter_978_);
                lean_closure_set(v___f_1020_, 1, v___f_1018_);
                lean_closure_set(v___f_1020_, 2, v___x_993_);
                lean_closure_set(v___f_1020_, 3, v___x_1019_);
                lean_closure_set(v___f_1020_, 4, v_monadInfo_992_);
                lean_closure_set(v___f_1020_, 5, v_body_979_);
                lean_closure_set(v___f_1020_, 6, v___y_1008_);
                lean_closure_set(v___f_1020_, 7, v_eType_x3f_1007_);
                if lean_obj_tag(v_eType_x3f_1007_) == 0 {
                    v___x_1021_ = 0;
                    v___x_1022_ = l_Lean_mkHole(v___x_994_, v___x_1021_);
                    v___y_996_ = v___y_1014_;
                    v___y_997_ = v___y_1012_;
                    v___y_998_ = v___f_1020_;
                    v___y_999_ = v___y_1009_;
                    v___y_1000_ = v___y_1013_;
                    v___y_1001_ = v___y_1010_;
                    v___y_1002_ = v___y_1011_;
                    v___y_1003_ = v___x_1022_;
                    state = 1;
                    continue;
                } else {
                    v_val_1023_ = lean_ctor_get(v_eType_x3f_1007_, 0);
                    lean_inc(v_val_1023_);
                    lean_dec_ref_known(v_eType_x3f_1007_, 1);
                    v___y_996_ = v___y_1014_;
                    v___y_997_ = v___y_1012_;
                    v___y_998_ = v___f_1020_;
                    v___y_999_ = v___y_1009_;
                    v___y_1000_ = v___y_1013_;
                    v___y_1001_ = v___y_1010_;
                    v___y_1002_ = v___y_1011_;
                    v___y_1003_ = v_val_1023_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___boxed(
    mut v_lifter_1032_: *mut LeanObject,
    mut v_body_1033_: *mut LeanObject,
    mut v_catch___1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1043_: *mut LeanObject = core::ptr::null_mut();
    v_res_1043_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(
        v_lifter_1032_,
        v_body_1033_,
        v_catch___1034_,
        v_a_1035_,
        v_a_1036_,
        v_a_1037_,
        v_a_1038_,
        v_a_1039_,
        v_a_1040_,
        v_a_1041_,
    );
    lean_dec(v_a_1041_);
    lean_dec_ref(v_a_1040_);
    lean_dec(v_a_1039_);
    lean_dec_ref(v_a_1038_);
    lean_dec(v_a_1037_);
    lean_dec_ref(v_a_1036_);
    lean_dec_ref(v_a_1035_);
    return v_res_1043_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoTry___lam__0(
    mut v_trySeq_1044_: *mut LeanObject,
    mut v___x_1045_: u8,
    mut v_cont_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
    mut v___y_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_Lean_Elab_Do_elabDoSeq(
        v_trySeq_1044_,
        v_cont_1046_,
        v___x_1045_,
        v___y_1047_,
        v___y_1048_,
        v___y_1049_,
        v___y_1050_,
        v___y_1051_,
        v___y_1052_,
        v___y_1053_,
    );
    return v___x_1055_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoTry___lam__0___boxed(
    mut v_trySeq_1056_: *mut LeanObject,
    mut v___x_1057_: *mut LeanObject,
    mut v_cont_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
    mut v___y_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
    mut v___y_1064_: *mut LeanObject,
    mut v___y_1065_: *mut LeanObject,
    mut v___y_1066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15837__boxed_1067_: u8 = 0;
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v___x_15837__boxed_1067_ = (lean_unbox(v___x_1057_) as u8);
    v_res_1068_ = l_Lean_Elab_Do_elabDoTry___lam__0(
        v_trySeq_1056_,
        v___x_15837__boxed_1067_,
        v_cont_1058_,
        v___y_1059_,
        v___y_1060_,
        v___y_1061_,
        v___y_1062_,
        v___y_1063_,
        v___y_1064_,
        v___y_1065_,
    );
    lean_dec(v___y_1065_);
    lean_dec_ref(v___y_1064_);
    lean_dec(v___y_1063_);
    lean_dec_ref(v___y_1062_);
    lean_dec(v___y_1061_);
    lean_dec_ref(v___y_1060_);
    lean_dec_ref(v___y_1059_);
    return v_res_1068_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3;
    v___x_1078_ = l_String_toRawSubstring_x27(v___x_1077_);
    return v___x_1078_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8()
-> *mut LeanObject {
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Array_mkArray0(lean_box(0));
    return v___x_1084_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(
    mut v_a_1112_: *mut LeanObject,
    mut v_as_1113_: *mut LeanObject,
    mut v_i_1114_: usize,
    mut v_stop_1115_: usize,
    mut v_b_1116_: *mut LeanObject,
    mut v___y_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: usize = 0;
    let mut v___x_1129_: usize = 0;
    let mut v___x_1131_: u8 = 0;
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u8 = 0;
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1131_ = lean_usize_dec_eq(v_i_1114_, v_stop_1115_);
                if v___x_1131_ == 0 {
                    v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1;
                    v___x_1133_ = lean_array_uget_borrowed(v_as_1113_, v_i_1114_);
                    lean_inc(v___x_1133_);
                    v___x_1134_ = l_Lean_Syntax_isOfKind(v___x_1133_, v___x_1132_);
                    if v___x_1134_ == 0 {
                        lean_inc(v___x_1133_);
                        lean_inc_ref(v_a_1112_);
                        v___x_1135_ =
                            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(
                                v_a_1112_,
                                v_b_1116_,
                                v___x_1133_,
                                v___y_1117_,
                                v___y_1118_,
                                v___y_1119_,
                                v___y_1120_,
                                v___y_1121_,
                                v___y_1122_,
                                v___y_1123_,
                            );
                        v___y_1126_ = v___x_1135_;
                        state = 1;
                        continue;
                    } else {
                        v_ref_1136_ = lean_ctor_get(v___y_1122_, 5);
                        v_quotContext_1137_ = lean_ctor_get(v___y_1122_, 10);
                        v_currMacroScope_1138_ = lean_ctor_get(v___y_1122_, 11);
                        v___x_1139_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4;
                        v___x_1140_ = lean_unsigned_to_nat(1);
                        v___x_1141_ = l_Lean_Syntax_getArg(v___x_1133_, v___x_1140_);
                        v___x_1142_ = l_Lean_SourceInfo_fromRef(v_ref_1136_, v___x_1131_);
                        v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2;
                        lean_inc_n(v___x_1142_, 12);
                        v___x_1144_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1144_, 0, v___x_1142_);
                        lean_ctor_set(v___x_1144_, 1, v___x_1143_);
                        v___x_1145_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4);
                        v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5;
                        lean_inc(v_currMacroScope_1138_);
                        lean_inc(v_quotContext_1137_);
                        v___x_1147_ = l_Lean_addMacroScope(
                            v_quotContext_1137_,
                            v___x_1146_,
                            v_currMacroScope_1138_,
                        );
                        v___x_1148_ = lean_box(0);
                        v___x_1149_ = lean_alloc_ctor(3, 4, (0) as u32);
                        lean_ctor_set(v___x_1149_, 0, v___x_1142_);
                        lean_ctor_set(v___x_1149_, 1, v___x_1145_);
                        lean_ctor_set(v___x_1149_, 2, v___x_1147_);
                        lean_ctor_set(v___x_1149_, 3, v___x_1148_);
                        v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7;
                        v___x_1151_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8);
                        v___x_1152_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_1152_, 0, v___x_1142_);
                        lean_ctor_set(v___x_1152_, 1, v___x_1150_);
                        lean_ctor_set(v___x_1152_, 2, v___x_1151_);
                        v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9;
                        v___x_1154_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1154_, 0, v___x_1142_);
                        lean_ctor_set(v___x_1154_, 1, v___x_1153_);
                        v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11;
                        v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13;
                        v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15;
                        v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16;
                        v___x_1159_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1159_, 0, v___x_1142_);
                        lean_ctor_set(v___x_1159_, 1, v___x_1158_);
                        v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18;
                        lean_inc_ref(v___x_1149_);
                        lean_inc_ref_n(v___x_1152_, 5);
                        v___x_1161_ =
                            l_Lean_Syntax_node2(v___x_1142_, v___x_1160_, v___x_1152_, v___x_1149_);
                        v___x_1162_ = l_Lean_Syntax_node1(v___x_1142_, v___x_1150_, v___x_1161_);
                        v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19;
                        v___x_1164_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1164_, 0, v___x_1142_);
                        lean_ctor_set(v___x_1164_, 1, v___x_1163_);
                        v___x_1165_ = l_Lean_Syntax_node7(
                            v___x_1142_,
                            v___x_1157_,
                            v___x_1159_,
                            v___x_1152_,
                            v___x_1152_,
                            v___x_1152_,
                            v___x_1162_,
                            v___x_1164_,
                            v___x_1141_,
                        );
                        v___x_1166_ =
                            l_Lean_Syntax_node2(v___x_1142_, v___x_1156_, v___x_1165_, v___x_1152_);
                        v___x_1167_ = l_Lean_Syntax_node1(v___x_1142_, v___x_1150_, v___x_1166_);
                        v___x_1168_ = l_Lean_Syntax_node1(v___x_1142_, v___x_1155_, v___x_1167_);
                        v___x_1169_ = l_Lean_Syntax_node5(
                            v___x_1142_,
                            v___x_1139_,
                            v___x_1144_,
                            v___x_1149_,
                            v___x_1152_,
                            v___x_1154_,
                            v___x_1168_,
                        );
                        lean_inc_ref(v_a_1112_);
                        v___x_1170_ =
                            l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(
                                v_a_1112_,
                                v_b_1116_,
                                v___x_1169_,
                                v___y_1117_,
                                v___y_1118_,
                                v___y_1119_,
                                v___y_1120_,
                                v___y_1121_,
                                v___y_1122_,
                                v___y_1123_,
                            );
                        v___y_1126_ = v___x_1170_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_1112_);
                    v___x_1171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1171_, 0, v_b_1116_);
                    return v___x_1171_;
                }
            }
            1 => {
                if lean_obj_tag(v___y_1126_) == 0 {
                    v_a_1127_ = lean_ctor_get(v___y_1126_, 0);
                    lean_inc(v_a_1127_);
                    lean_dec_ref_known(v___y_1126_, 1);
                    v___x_1128_ = 1usize;
                    v___x_1129_ = lean_usize_add(v_i_1114_, v___x_1128_);
                    v_i_1114_ = v___x_1129_;
                    v_b_1116_ = v_a_1127_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_1112_);
                    return v___y_1126_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___boxed(
    mut v_a_1172_: *mut LeanObject,
    mut v_as_1173_: *mut LeanObject,
    mut v_i_1174_: *mut LeanObject,
    mut v_stop_1175_: *mut LeanObject,
    mut v_b_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
    mut v___y_1181_: *mut LeanObject,
    mut v___y_1182_: *mut LeanObject,
    mut v___y_1183_: *mut LeanObject,
    mut v___y_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1185_: usize = 0;
    let mut v_stop_boxed_1186_: usize = 0;
    let mut v_res_1187_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1185_ = lean_unbox_usize(v_i_1174_);
    lean_dec(v_i_1174_);
    v_stop_boxed_1186_ = lean_unbox_usize(v_stop_1175_);
    lean_dec(v_stop_1175_);
    v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(v_a_1172_, v_as_1173_, v_i_boxed_1185_, v_stop_boxed_1186_, v_b_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
    lean_dec(v___y_1183_);
    lean_dec_ref(v___y_1182_);
    lean_dec(v___y_1181_);
    lean_dec_ref(v___y_1180_);
    lean_dec(v___y_1179_);
    lean_dec_ref(v___y_1178_);
    lean_dec_ref(v___y_1177_);
    lean_dec_ref(v_as_1173_);
    return v_res_1187_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(
    mut v_msgData_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
    mut v___y_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    v___x_1194_ = lean_st_ref_get(v___y_1192_);
    v_env_1195_ = lean_ctor_get(v___x_1194_, 0);
    lean_inc_ref(v_env_1195_);
    lean_dec(v___x_1194_);
    v___x_1196_ = lean_st_ref_get(v___y_1190_);
    v_mctx_1197_ = lean_ctor_get(v___x_1196_, 0);
    lean_inc_ref(v_mctx_1197_);
    lean_dec(v___x_1196_);
    v_lctx_1198_ = lean_ctor_get(v___y_1189_, 2);
    v_options_1199_ = lean_ctor_get(v___y_1191_, 2);
    lean_inc_ref(v_options_1199_);
    lean_inc_ref(v_lctx_1198_);
    v___x_1200_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1200_, 0, v_env_1195_);
    lean_ctor_set(v___x_1200_, 1, v_mctx_1197_);
    lean_ctor_set(v___x_1200_, 2, v_lctx_1198_);
    lean_ctor_set(v___x_1200_, 3, v_options_1199_);
    v___x_1201_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1201_, 0, v___x_1200_);
    lean_ctor_set(v___x_1201_, 1, v_msgData_1188_);
    v___x_1202_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1202_, 0, v___x_1201_);
    return v___x_1202_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4___boxed(
    mut v_msgData_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1209_: *mut LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msgData_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
    lean_dec(v___y_1207_);
    lean_dec_ref(v___y_1206_);
    lean_dec(v___y_1205_);
    lean_dec_ref(v___y_1204_);
    return v_res_1209_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(
    mut v_msg_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1216_ = lean_ctor_get(v___y_1213_, 5);
                v___x_1217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msg_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
                v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
                v_isSharedCheck_1226_ = (!lean_is_exclusive(v___x_1217_)) as u8;
                if v_isSharedCheck_1226_ == 0 {
                    v___x_1220_ = v___x_1217_;
                    v_isShared_1221_ = v_isSharedCheck_1226_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1218_);
                    lean_dec(v___x_1217_);
                    v___x_1220_ = lean_box(0);
                    v_isShared_1221_ = v_isSharedCheck_1226_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1216_);
                v___x_1222_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1222_, 0, v_ref_1216_);
                lean_ctor_set(v___x_1222_, 1, v_a_1218_);
                if v_isShared_1221_ == 0 {
                    lean_ctor_set_tag(v___x_1220_, 1);
                    lean_ctor_set(v___x_1220_, 0, v___x_1222_);
                    v___x_1224_ = v___x_1220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg___boxed(
    mut v_msg_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1233_: *mut LeanObject = core::ptr::null_mut();
    v_res_1233_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(
        v_msg_1227_,
        v___y_1228_,
        v___y_1229_,
        v___y_1230_,
        v___y_1231_,
    );
    lean_dec(v___y_1231_);
    lean_dec_ref(v___y_1230_);
    lean_dec(v___y_1229_);
    lean_dec_ref(v___y_1228_);
    return v_res_1233_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(
    mut v_as_1237_: *mut LeanObject,
    mut v_i_1238_: usize,
    mut v_stop_1239_: usize,
    mut v_b_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: u8 = 0;
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: u8 = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u8 = 0;
    let mut v___x_1259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1246_ = lean_usize_dec_eq(v_i_1238_, v_stop_1239_);
                if v___x_1246_ == 0 {
                    v___x_1247_ = lean_array_uget_borrowed(v_as_1237_, v_i_1238_);
                    v___x_1248_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4;
                    lean_inc(v___x_1247_);
                    v___x_1249_ = l_Lean_Syntax_isOfKind(v___x_1247_, v___x_1248_);
                    if v___x_1249_ == 0 {
                        v___y_1242_ = v_b_1240_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1250_ = lean_unsigned_to_nat(1);
                        v_x_1251_ = l_Lean_Syntax_getArg(v___x_1247_, v___x_1250_);
                        v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1;
                        lean_inc(v_x_1251_);
                        v___x_1255_ = l_Lean_Syntax_isOfKind(v_x_1251_, v___x_1254_);
                        if v___x_1255_ == 0 {
                            lean_dec(v_x_1251_);
                            v___y_1242_ = v_b_1240_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1256_ = lean_unsigned_to_nat(2);
                            v___x_1257_ = l_Lean_Syntax_getArg(v___x_1247_, v___x_1256_);
                            v___x_1258_ = l_Lean_Syntax_isNone(v___x_1257_);
                            if v___x_1258_ == 0 {
                                v___x_1259_ = l_Lean_Syntax_matchesNull(v___x_1257_, v___x_1256_);
                                if v___x_1259_ == 0 {
                                    lean_dec(v_x_1251_);
                                    v___y_1242_ = v_b_1240_;
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1257_);
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    return v_b_1240_;
                }
            }
            1 => {
                v___x_1243_ = 1usize;
                v___x_1244_ = lean_usize_add(v_i_1238_, v___x_1243_);
                v_i_1238_ = v___x_1244_;
                v_b_1240_ = v___y_1242_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1253_ = lean_array_push(v_b_1240_, v_x_1251_);
                v___y_1242_ = v___x_1253_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___boxed(
    mut v_as_1260_: *mut LeanObject,
    mut v_i_1261_: *mut LeanObject,
    mut v_stop_1262_: *mut LeanObject,
    mut v_b_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1264_: usize = 0;
    let mut v_stop_boxed_1265_: usize = 0;
    let mut v_res_1266_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1264_ = lean_unbox_usize(v_i_1261_);
    lean_dec(v_i_1261_);
    v_stop_boxed_1265_ = lean_unbox_usize(v_stop_1262_);
    lean_dec(v_stop_1262_);
    v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(v_as_1260_, v_i_boxed_1264_, v_stop_boxed_1265_, v_b_1263_);
    lean_dec_ref(v_as_1260_);
    return v_res_1266_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(
    mut v_as_1269_: *mut LeanObject,
    mut v_start_1270_: *mut LeanObject,
    mut v_stop_1271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    v___x_1272_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0;
    v___x_1273_ = lean_nat_dec_lt(v_start_1270_, v_stop_1271_);
    if v___x_1273_ == 0 {
        return v___x_1272_;
    } else {
        let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: u8 = 0;
        v___x_1274_ = lean_array_get_size(v_as_1269_);
        v___x_1275_ = lean_nat_dec_le(v_stop_1271_, v___x_1274_);
        if v___x_1275_ == 0 {
            let mut v___x_1276_: u8 = 0;
            v___x_1276_ = lean_nat_dec_lt(v_start_1270_, v___x_1274_);
            if v___x_1276_ == 0 {
                return v___x_1272_;
            } else {
                let mut v___x_1277_: usize = 0;
                let mut v___x_1278_: usize = 0;
                let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
                v___x_1277_ = lean_usize_of_nat(v_start_1270_);
                v___x_1278_ = lean_usize_of_nat(v___x_1274_);
                v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(v_as_1269_, v___x_1277_, v___x_1278_, v___x_1272_);
                return v___x_1279_;
            }
        } else {
            let mut v___x_1280_: usize = 0;
            let mut v___x_1281_: usize = 0;
            let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
            v___x_1280_ = lean_usize_of_nat(v_start_1270_);
            v___x_1281_ = lean_usize_of_nat(v_stop_1271_);
            v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(v_as_1269_, v___x_1280_, v___x_1281_, v___x_1272_);
            return v___x_1282_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___boxed(
    mut v_as_1283_: *mut LeanObject,
    mut v_start_1284_: *mut LeanObject,
    mut v_stop_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1286_: *mut LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(
        v_as_1283_,
        v_start_1284_,
        v_stop_1285_,
    );
    lean_dec(v_stop_1285_);
    lean_dec(v_start_1284_);
    lean_dec_ref(v_as_1283_);
    return v_res_1286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(
    mut v_sz_1287_: usize,
    mut v_i_1288_: usize,
    mut v_bs_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1290_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
                if v___x_1290_ == 0 {
                    v___x_1291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1291_, 0, v_bs_1289_);
                    return v___x_1291_;
                } else {
                    v_v_1292_ = lean_array_uget(v_bs_1289_, v_i_1288_);
                    v___x_1293_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1294_ = lean_array_uset(v_bs_1289_, v_i_1288_, v___x_1293_);
                    v___x_1295_ = 1usize;
                    v___x_1296_ = lean_usize_add(v_i_1288_, v___x_1295_);
                    v___x_1297_ = lean_array_uset(v_bs_x27_1294_, v_i_1288_, v_v_1292_);
                    v_i_1288_ = v___x_1296_;
                    v_bs_1289_ = v___x_1297_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0___boxed(
    mut v_sz_1299_: *mut LeanObject,
    mut v_i_1300_: *mut LeanObject,
    mut v_bs_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1302_: usize = 0;
    let mut v_i_boxed_1303_: usize = 0;
    let mut v_res_1304_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1302_ = lean_unbox_usize(v_sz_1299_);
    lean_dec(v_sz_1299_);
    v_i_boxed_1303_ = lean_unbox_usize(v_i_1300_);
    lean_dec(v_i_1300_);
    v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_boxed_1302_, v_i_boxed_1303_, v_bs_1301_);
    return v_res_1304_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoTry___closed__11() -> *mut LeanObject {
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    v___x_1324_ = l_Lean_Elab_Do_elabDoTry___closed__10;
    v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoTry(
    mut v_stx_1332_: *mut LeanObject,
    mut v_dec_1333_: *mut LeanObject,
    mut v_a_1334_: *mut LeanObject,
    mut v_a_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
    mut v_a_1337_: *mut LeanObject,
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___y_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_liftedDoBlockResultType_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_a_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1433_: usize = 0;
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: u8 = 0;
    let mut v___x_1462_: usize = 0;
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: usize = 0;
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1469_: u8 = 0;
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut v_a_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1481_: u8 = 0;
    let mut v___y_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trySeq_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finSeq_x3f_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v_a_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finSeq_x3f_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1363_ = l_Lean_Elab_Do_elabDoTry___closed__1;
                lean_inc(v_stx_1332_);
                v___x_1364_ = l_Lean_Syntax_isOfKind(v_stx_1332_, v___x_1363_);
                if v___x_1364_ == 0 {
                    lean_dec_ref(v_dec_1333_);
                    lean_dec(v_stx_1332_);
                    v___x_1429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
                    return v___x_1429_;
                } else {
                    v___x_1430_ = lean_unsigned_to_nat(2);
                    v___x_1431_ = l_Lean_Syntax_getArg(v_stx_1332_, v___x_1430_);
                    v___x_1432_ = l_Lean_Syntax_getArgs(v___x_1431_);
                    lean_dec(v___x_1431_);
                    v_sz_1433_ = lean_array_size(v___x_1432_);
                    v___x_1434_ = 0usize;
                    v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_1433_, v___x_1434_, v___x_1432_);
                    if lean_obj_tag(v___x_1435_) == 0 {
                        lean_dec_ref(v_dec_1333_);
                        lean_dec(v_stx_1332_);
                        v___x_1436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
                        return v___x_1436_;
                    } else {
                        v_val_1437_ = lean_ctor_get(v___x_1435_, 0);
                        v_isSharedCheck_1543_ = (!lean_is_exclusive(v___x_1435_)) as u8;
                        if v_isSharedCheck_1543_ == 0 {
                            v___x_1439_ = v___x_1435_;
                            v_isShared_1440_ = v_isSharedCheck_1543_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_val_1437_);
                            lean_dec(v___x_1435_);
                            v___x_1439_ = lean_box(0);
                            v_isShared_1440_ = v_isSharedCheck_1543_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1352_ = l_Lean_Elab_Do_ControlLifter_restoreCont(
                    v___y_1343_,
                    v___y_1345_,
                    v___y_1346_,
                    v___y_1347_,
                    v___y_1348_,
                    v___y_1349_,
                    v___y_1350_,
                    v___y_1351_,
                );
                if lean_obj_tag(v___x_1352_) == 0 {
                    v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
                    lean_inc(v_a_1353_);
                    lean_dec_ref_known(v___x_1352_, 1);
                    v___x_1354_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(
                        v_a_1353_,
                        v_body_1344_,
                        v___y_1345_,
                        v___y_1346_,
                        v___y_1347_,
                        v___y_1348_,
                        v___y_1349_,
                        v___y_1350_,
                        v___y_1351_,
                    );
                    return v___x_1354_;
                } else {
                    lean_dec_ref(v_body_1344_);
                    v_a_1355_ = lean_ctor_get(v___x_1352_, 0);
                    v_isSharedCheck_1362_ = (!lean_is_exclusive(v___x_1352_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1357_ = v___x_1352_;
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1355_);
                        lean_dec(v___x_1352_);
                        v___x_1357_ = lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1358_ == 0 {
                    v___x_1360_ = v___x_1357_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
                    v___x_1360_ = v_reuseFailAlloc_1361_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1360_;
            }
            4 => {
                if lean_obj_tag(v___y_1376_) == 0 {
                    if lean_obj_tag(v___y_1373_) == 0 {
                        v_a_1377_ = lean_ctor_get(v___y_1376_, 0);
                        lean_inc(v_a_1377_);
                        lean_dec_ref_known(v___y_1376_, 1);
                        v___y_1343_ = v___y_1374_;
                        v_body_1344_ = v_a_1377_;
                        v___y_1345_ = v___y_1371_;
                        v___y_1346_ = v___y_1370_;
                        v___y_1347_ = v___y_1375_;
                        v___y_1348_ = v___y_1367_;
                        v___y_1349_ = v___y_1369_;
                        v___y_1350_ = v___y_1372_;
                        v___y_1351_ = v___y_1368_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1378_ = lean_ctor_get(v___y_1376_, 0);
                        lean_inc(v_a_1378_);
                        lean_dec_ref_known(v___y_1376_, 1);
                        v_val_1379_ = lean_ctor_get(v___y_1373_, 0);
                        lean_inc(v_val_1379_);
                        lean_dec_ref_known(v___y_1373_, 1);
                        v___x_1380_ = l_Lean_Elab_Do_elabDoTry___closed__3;
                        v___x_1381_ = 0;
                        v___x_1382_ = l_Lean_Elab_Do_mkFreshResultType___redArg(
                            v___x_1380_,
                            v___x_1381_,
                            v___y_1371_,
                            v___y_1367_,
                            v___y_1369_,
                            v___y_1372_,
                            v___y_1368_,
                        );
                        if lean_obj_tag(v___x_1382_) == 0 {
                            v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
                            lean_inc(v_a_1383_);
                            lean_dec_ref_known(v___x_1382_, 1);
                            v___x_1384_ = l_Lean_Expr_mvarId_x21(v_a_1383_);
                            lean_inc(v_val_1379_);
                            v___x_1385_ = l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(
                                v___x_1384_,
                                v_val_1379_,
                                v___y_1375_,
                            );
                            if lean_obj_tag(v___x_1385_) == 0 {
                                lean_dec_ref_known(v___x_1385_, 1);
                                lean_inc(v_a_1383_);
                                v___x_1386_ = l_Lean_Elab_Do_DoElemCont_mkPure___redArg(
                                    v_a_1383_,
                                    v___y_1372_,
                                    v___y_1368_,
                                );
                                if lean_obj_tag(v___x_1386_) == 0 {
                                    v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
                                    lean_inc(v_a_1387_);
                                    lean_dec_ref_known(v___x_1386_, 1);
                                    v___x_1388_ = lean_box((v___x_1364_) as usize);
                                    v___x_1389_ = lean_alloc_closure(
                                        l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
                                        11,
                                        3,
                                    );
                                    lean_closure_set(v___x_1389_, 0, v_val_1379_);
                                    lean_closure_set(v___x_1389_, 1, v_a_1387_);
                                    lean_closure_set(v___x_1389_, 2, v___x_1388_);
                                    lean_inc(v_a_1383_);
                                    v___x_1390_ = l_Lean_Elab_Do_enterFinally(
                                        v_a_1383_,
                                        v___x_1389_,
                                        v___y_1371_,
                                        v___y_1370_,
                                        v___y_1375_,
                                        v___y_1367_,
                                        v___y_1369_,
                                        v___y_1372_,
                                        v___y_1368_,
                                    );
                                    if lean_obj_tag(v___x_1390_) == 0 {
                                        v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
                                        lean_inc(v_a_1391_);
                                        lean_dec_ref_known(v___x_1390_, 1);
                                        v_m_1392_ = lean_ctor_get(v___y_1366_, 0);
                                        v_u_1393_ = lean_ctor_get(v___y_1366_, 1);
                                        v_v_1394_ = lean_ctor_get(v___y_1366_, 2);
                                        v___x_1395_ = l_Lean_Elab_Do_elabDoTry___closed__5;
                                        v___x_1396_ = lean_box(0);
                                        lean_inc(v_v_1394_);
                                        v___x_1397_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_1397_, 0, v_v_1394_);
                                        lean_ctor_set(v___x_1397_, 1, v___x_1396_);
                                        lean_inc(v_u_1393_);
                                        v___x_1398_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_1398_, 0, v_u_1393_);
                                        lean_ctor_set(v___x_1398_, 1, v___x_1397_);
                                        lean_inc_ref(v___x_1398_);
                                        v___x_1399_ = l_Lean_mkConst(v___x_1395_, v___x_1398_);
                                        lean_inc_ref(v_m_1392_);
                                        v___x_1400_ =
                                            l_Lean_Expr_app___override(v___x_1399_, v_m_1392_);
                                        v___x_1401_ = lean_box(0);
                                        v___x_1402_ = l_Lean_Elab_Term_mkInstMVar(
                                            v___x_1400_,
                                            v___x_1401_,
                                            v___y_1370_,
                                            v___y_1375_,
                                            v___y_1367_,
                                            v___y_1369_,
                                            v___y_1372_,
                                            v___y_1368_,
                                        );
                                        if lean_obj_tag(v___x_1402_) == 0 {
                                            v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
                                            lean_inc(v_a_1403_);
                                            lean_dec_ref_known(v___x_1402_, 1);
                                            v___x_1404_ = l_Lean_Elab_Do_elabDoTry___closed__7;
                                            lean_inc_ref(v___x_1398_);
                                            v___x_1405_ = l_Lean_mkConst(v___x_1404_, v___x_1398_);
                                            lean_inc_ref(v_m_1392_);
                                            v___x_1406_ =
                                                l_Lean_Expr_app___override(v___x_1405_, v_m_1392_);
                                            v___x_1407_ = l_Lean_Elab_Term_mkInstMVar(
                                                v___x_1406_,
                                                v___x_1401_,
                                                v___y_1370_,
                                                v___y_1375_,
                                                v___y_1367_,
                                                v___y_1369_,
                                                v___y_1372_,
                                                v___y_1368_,
                                            );
                                            if lean_obj_tag(v___x_1407_) == 0 {
                                                v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
                                                lean_inc(v_a_1408_);
                                                lean_dec_ref_known(v___x_1407_, 1);
                                                v_liftedDoBlockResultType_1409_ =
                                                    lean_ctor_get(v___y_1374_, 5);
                                                v___x_1410_ = l_Lean_Elab_Do_elabDoTry___closed__9;
                                                v___x_1411_ =
                                                    l_Lean_mkConst(v___x_1410_, v___x_1398_);
                                                lean_inc_ref(v_liftedDoBlockResultType_1409_);
                                                lean_inc_ref(v_m_1392_);
                                                v___x_1412_ = l_Lean_mkApp7(
                                                    v___x_1411_,
                                                    v_m_1392_,
                                                    v_liftedDoBlockResultType_1409_,
                                                    v_a_1383_,
                                                    v_a_1403_,
                                                    v_a_1408_,
                                                    v_a_1378_,
                                                    v_a_1391_,
                                                );
                                                v___y_1343_ = v___y_1374_;
                                                v_body_1344_ = v___x_1412_;
                                                v___y_1345_ = v___y_1371_;
                                                v___y_1346_ = v___y_1370_;
                                                v___y_1347_ = v___y_1375_;
                                                v___y_1348_ = v___y_1367_;
                                                v___y_1349_ = v___y_1369_;
                                                v___y_1350_ = v___y_1372_;
                                                v___y_1351_ = v___y_1368_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec(v_a_1403_);
                                                lean_dec_ref_known(v___x_1398_, 2);
                                                lean_dec(v_a_1391_);
                                                lean_dec(v_a_1383_);
                                                lean_dec(v_a_1378_);
                                                lean_dec_ref(v___y_1374_);
                                                return v___x_1407_;
                                            }
                                        } else {
                                            lean_dec_ref_known(v___x_1398_, 2);
                                            lean_dec(v_a_1391_);
                                            lean_dec(v_a_1383_);
                                            lean_dec(v_a_1378_);
                                            lean_dec_ref(v___y_1374_);
                                            return v___x_1402_;
                                        }
                                    } else {
                                        lean_dec(v_a_1383_);
                                        lean_dec(v_a_1378_);
                                        lean_dec_ref(v___y_1374_);
                                        return v___x_1390_;
                                    }
                                } else {
                                    lean_dec(v_a_1383_);
                                    lean_dec(v_val_1379_);
                                    lean_dec(v_a_1378_);
                                    lean_dec_ref(v___y_1374_);
                                    v_a_1413_ = lean_ctor_get(v___x_1386_, 0);
                                    v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1386_)) as u8;
                                    if v_isSharedCheck_1420_ == 0 {
                                        v___x_1415_ = v___x_1386_;
                                        v_isShared_1416_ = v_isSharedCheck_1420_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1413_);
                                        lean_dec(v___x_1386_);
                                        v___x_1415_ = lean_box(0);
                                        v_isShared_1416_ = v_isSharedCheck_1420_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_1383_);
                                lean_dec(v_val_1379_);
                                lean_dec(v_a_1378_);
                                lean_dec_ref(v___y_1374_);
                                v_a_1421_ = lean_ctor_get(v___x_1385_, 0);
                                v_isSharedCheck_1428_ = (!lean_is_exclusive(v___x_1385_)) as u8;
                                if v_isSharedCheck_1428_ == 0 {
                                    v___x_1423_ = v___x_1385_;
                                    v_isShared_1424_ = v_isSharedCheck_1428_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1421_);
                                    lean_dec(v___x_1385_);
                                    v___x_1423_ = lean_box(0);
                                    v_isShared_1424_ = v_isSharedCheck_1428_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_1379_);
                            lean_dec(v_a_1378_);
                            lean_dec_ref(v___y_1374_);
                            return v___x_1382_;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_1374_);
                    lean_dec(v___y_1373_);
                    return v___y_1376_;
                }
            }
            5 => {
                if v_isShared_1416_ == 0 {
                    v___x_1418_ = v___x_1415_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1418_;
            }
            7 => {
                if v_isShared_1424_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
                    v___x_1426_ = v_reuseFailAlloc_1427_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1426_;
            }
            9 => {
                v___x_1441_ = lean_unsigned_to_nat(0);
                v___x_1504_ = lean_unsigned_to_nat(1);
                v_trySeq_1505_ = l_Lean_Syntax_getArg(v_stx_1332_, v___x_1504_);
                v___x_1506_ = lean_box((v___x_1364_) as usize);
                v___f_1507_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoTry___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    2,
                );
                lean_closure_set(v___f_1507_, 0, v_trySeq_1505_);
                lean_closure_set(v___f_1507_, 1, v___x_1506_);
                v___x_1529_ = lean_unsigned_to_nat(3);
                v___x_1530_ = l_Lean_Syntax_getArg(v_stx_1332_, v___x_1529_);
                v___x_1531_ = l_Lean_Syntax_isNone(v___x_1530_);
                if v___x_1531_ == 0 {
                    lean_inc(v___x_1530_);
                    v___x_1532_ = l_Lean_Syntax_matchesNull(v___x_1530_, v___x_1504_);
                    if v___x_1532_ == 0 {
                        lean_dec(v___x_1530_);
                        lean_dec_ref(v___f_1507_);
                        lean_del_object(v___x_1439_);
                        lean_dec(v_val_1437_);
                        lean_dec_ref(v_dec_1333_);
                        lean_dec(v_stx_1332_);
                        v___x_1533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
                        return v___x_1533_;
                    } else {
                        v___x_1534_ = l_Lean_Syntax_getArg(v___x_1530_, v___x_1441_);
                        lean_dec(v___x_1530_);
                        v___x_1535_ = l_Lean_Elab_Do_elabDoTry___closed__13;
                        lean_inc(v___x_1534_);
                        v___x_1536_ = l_Lean_Syntax_isOfKind(v___x_1534_, v___x_1535_);
                        if v___x_1536_ == 0 {
                            lean_dec(v___x_1534_);
                            lean_dec_ref(v___f_1507_);
                            lean_del_object(v___x_1439_);
                            lean_dec(v_val_1437_);
                            lean_dec_ref(v_dec_1333_);
                            lean_dec(v_stx_1332_);
                            v___x_1537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
                            return v___x_1537_;
                        } else {
                            v_finSeq_x3f_1538_ = l_Lean_Syntax_getArg(v___x_1534_, v___x_1504_);
                            lean_dec(v___x_1534_);
                            if v_isShared_1440_ == 0 {
                                lean_ctor_set(v___x_1439_, 0, v_finSeq_x3f_1538_);
                                v___x_1540_ = v___x_1439_;
                                state = 21;
                                continue;
                            } else {
                                v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_finSeq_x3f_1538_);
                                v___x_1540_ = v_reuseFailAlloc_1541_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_1530_);
                    lean_del_object(v___x_1439_);
                    v___x_1542_ = lean_box(0);
                    v_finSeq_x3f_1509_ = v___x_1542_;
                    v___y_1510_ = v_a_1334_;
                    v___y_1511_ = v_a_1335_;
                    v___y_1512_ = v_a_1336_;
                    v___y_1513_ = v_a_1337_;
                    v___y_1514_ = v_a_1338_;
                    v___y_1515_ = v_a_1339_;
                    v___y_1516_ = v_a_1340_;
                    state = 18;
                    continue;
                }
            }
            10 => {
                v___x_1453_ = l_Lean_Elab_Do_inferControlInfoElem(
                    v_stx_1332_,
                    v___y_1447_,
                    v___y_1448_,
                    v___y_1449_,
                    v___y_1450_,
                    v___y_1451_,
                    v___y_1452_,
                );
                if lean_obj_tag(v___x_1453_) == 0 {
                    v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
                    lean_inc(v_a_1454_);
                    lean_dec_ref_known(v___x_1453_, 1);
                    v___x_1455_ = l_Lean_Elab_Do_ControlLifter_ofCont(
                        v_a_1454_,
                        v_dec_1333_,
                        v___y_1446_,
                        v___y_1447_,
                        v___y_1448_,
                        v___y_1449_,
                        v___y_1450_,
                        v___y_1451_,
                        v___y_1452_,
                    );
                    lean_dec(v_a_1454_);
                    if lean_obj_tag(v___x_1455_) == 0 {
                        v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
                        lean_inc_n(v_a_1456_, 2);
                        lean_dec_ref_known(v___x_1455_, 1);
                        v___x_1457_ = l_Lean_Elab_Do_ControlLifter_lift(
                            v_a_1456_,
                            v___y_1444_,
                            v___y_1446_,
                            v___y_1447_,
                            v___y_1448_,
                            v___y_1449_,
                            v___y_1450_,
                            v___y_1451_,
                            v___y_1452_,
                        );
                        if lean_obj_tag(v___x_1457_) == 0 {
                            v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
                            lean_inc(v_a_1458_);
                            v_monadInfo_1459_ = lean_ctor_get(v___y_1446_, 0);
                            v___x_1460_ = lean_nat_dec_lt(v___x_1441_, v___y_1445_);
                            if v___x_1460_ == 0 {
                                lean_dec(v_a_1458_);
                                lean_dec(v___y_1445_);
                                lean_dec(v_val_1437_);
                                v___y_1366_ = v_monadInfo_1459_;
                                v___y_1367_ = v___y_1449_;
                                v___y_1368_ = v___y_1452_;
                                v___y_1369_ = v___y_1450_;
                                v___y_1370_ = v___y_1447_;
                                v___y_1371_ = v___y_1446_;
                                v___y_1372_ = v___y_1451_;
                                v___y_1373_ = v___y_1443_;
                                v___y_1374_ = v_a_1456_;
                                v___y_1375_ = v___y_1448_;
                                v___y_1376_ = v___x_1457_;
                                state = 4;
                                continue;
                            } else {
                                v___x_1461_ = lean_nat_dec_le(v___y_1445_, v___y_1445_);
                                if v___x_1461_ == 0 {
                                    if v___x_1460_ == 0 {
                                        lean_dec(v_a_1458_);
                                        lean_dec(v___y_1445_);
                                        lean_dec(v_val_1437_);
                                        v___y_1366_ = v_monadInfo_1459_;
                                        v___y_1367_ = v___y_1449_;
                                        v___y_1368_ = v___y_1452_;
                                        v___y_1369_ = v___y_1450_;
                                        v___y_1370_ = v___y_1447_;
                                        v___y_1371_ = v___y_1446_;
                                        v___y_1372_ = v___y_1451_;
                                        v___y_1373_ = v___y_1443_;
                                        v___y_1374_ = v_a_1456_;
                                        v___y_1375_ = v___y_1448_;
                                        v___y_1376_ = v___x_1457_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec_ref_known(v___x_1457_, 1);
                                        v___x_1462_ = lean_usize_of_nat(v___y_1445_);
                                        lean_dec(v___y_1445_);
                                        lean_inc(v_a_1456_);
                                        v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(v_a_1456_, v_val_1437_, v___x_1434_, v___x_1462_, v_a_1458_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
                                        lean_dec(v_val_1437_);
                                        v___y_1366_ = v_monadInfo_1459_;
                                        v___y_1367_ = v___y_1449_;
                                        v___y_1368_ = v___y_1452_;
                                        v___y_1369_ = v___y_1450_;
                                        v___y_1370_ = v___y_1447_;
                                        v___y_1371_ = v___y_1446_;
                                        v___y_1372_ = v___y_1451_;
                                        v___y_1373_ = v___y_1443_;
                                        v___y_1374_ = v_a_1456_;
                                        v___y_1375_ = v___y_1448_;
                                        v___y_1376_ = v___x_1463_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_1457_, 1);
                                    v___x_1464_ = lean_usize_of_nat(v___y_1445_);
                                    lean_dec(v___y_1445_);
                                    lean_inc(v_a_1456_);
                                    v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(v_a_1456_, v_val_1437_, v___x_1434_, v___x_1464_, v_a_1458_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
                                    lean_dec(v_val_1437_);
                                    v___y_1366_ = v_monadInfo_1459_;
                                    v___y_1367_ = v___y_1449_;
                                    v___y_1368_ = v___y_1452_;
                                    v___y_1369_ = v___y_1450_;
                                    v___y_1370_ = v___y_1447_;
                                    v___y_1371_ = v___y_1446_;
                                    v___y_1372_ = v___y_1451_;
                                    v___y_1373_ = v___y_1443_;
                                    v___y_1374_ = v_a_1456_;
                                    v___y_1375_ = v___y_1448_;
                                    v___y_1376_ = v___x_1465_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1456_);
                            lean_dec(v___y_1445_);
                            lean_dec(v___y_1443_);
                            lean_dec(v_val_1437_);
                            return v___x_1457_;
                        }
                    } else {
                        lean_dec(v___y_1445_);
                        lean_dec_ref(v___y_1444_);
                        lean_dec(v___y_1443_);
                        lean_dec(v_val_1437_);
                        v_a_1466_ = lean_ctor_get(v___x_1455_, 0);
                        v_isSharedCheck_1473_ = (!lean_is_exclusive(v___x_1455_)) as u8;
                        if v_isSharedCheck_1473_ == 0 {
                            v___x_1468_ = v___x_1455_;
                            v_isShared_1469_ = v_isSharedCheck_1473_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_1466_);
                            lean_dec(v___x_1455_);
                            v___x_1468_ = lean_box(0);
                            v_isShared_1469_ = v_isSharedCheck_1473_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1445_);
                    lean_dec_ref(v___y_1444_);
                    lean_dec(v___y_1443_);
                    lean_dec(v_val_1437_);
                    lean_dec_ref(v_dec_1333_);
                    v_a_1474_ = lean_ctor_get(v___x_1453_, 0);
                    v_isSharedCheck_1481_ = (!lean_is_exclusive(v___x_1453_)) as u8;
                    if v_isSharedCheck_1481_ == 0 {
                        v___x_1476_ = v___x_1453_;
                        v_isShared_1477_ = v_isSharedCheck_1481_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_1474_);
                        lean_dec(v___x_1453_);
                        v___x_1476_ = lean_box(0);
                        v_isShared_1477_ = v_isSharedCheck_1481_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1469_ == 0 {
                    v___x_1471_ = v___x_1468_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
                    v___x_1471_ = v_reuseFailAlloc_1472_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1471_;
            }
            13 => {
                if v_isShared_1477_ == 0 {
                    v___x_1479_ = v___x_1476_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
                    v___x_1479_ = v_reuseFailAlloc_1480_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1479_;
            }
            15 => {
                if v___y_1493_ == 0 {
                    v___y_1443_ = v___y_1487_;
                    v___y_1444_ = v___y_1486_;
                    v___y_1445_ = v___y_1491_;
                    v___y_1446_ = v___y_1484_;
                    v___y_1447_ = v___y_1483_;
                    v___y_1448_ = v___y_1490_;
                    v___y_1449_ = v___y_1492_;
                    v___y_1450_ = v___y_1489_;
                    v___y_1451_ = v___y_1488_;
                    v___y_1452_ = v___y_1485_;
                    state = 10;
                    continue;
                } else {
                    lean_dec(v___y_1491_);
                    lean_dec(v___y_1487_);
                    lean_dec_ref(v___y_1486_);
                    lean_dec(v_val_1437_);
                    lean_dec_ref(v_dec_1333_);
                    lean_dec(v_stx_1332_);
                    v___x_1494_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoTry___closed__11),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoTry___closed__11_once),
                        _init_l_Lean_Elab_Do_elabDoTry___closed__11,
                    );
                    v___x_1495_ =
                        l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(
                            v___x_1494_,
                            v___y_1492_,
                            v___y_1489_,
                            v___y_1488_,
                            v___y_1485_,
                        );
                    v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
                    v_isSharedCheck_1503_ = (!lean_is_exclusive(v___x_1495_)) as u8;
                    if v_isSharedCheck_1503_ == 0 {
                        v___x_1498_ = v___x_1495_;
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_1496_);
                        lean_dec(v___x_1495_);
                        v___x_1498_ = lean_box(0);
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_1499_ == 0 {
                    v___x_1501_ = v___x_1498_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
                    v___x_1501_ = v_reuseFailAlloc_1502_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1501_;
            }
            18 => {
                v___x_1517_ = lean_array_get_size(v_val_1437_);
                v___x_1518_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(
                    v_val_1437_,
                    v___x_1441_,
                    v___x_1517_,
                );
                v___x_1519_ = l_Lean_Elab_Do_checkMutVarsForShadowing(
                    v___x_1518_,
                    v___y_1510_,
                    v___y_1511_,
                    v___y_1512_,
                    v___y_1513_,
                    v___y_1514_,
                    v___y_1515_,
                    v___y_1516_,
                );
                lean_dec_ref(v___x_1518_);
                if lean_obj_tag(v___x_1519_) == 0 {
                    lean_dec_ref_known(v___x_1519_, 1);
                    v___x_1520_ = lean_nat_dec_eq(v___x_1517_, v___x_1441_);
                    if v___x_1520_ == 0 {
                        v___y_1483_ = v___y_1511_;
                        v___y_1484_ = v___y_1510_;
                        v___y_1485_ = v___y_1516_;
                        v___y_1486_ = v___f_1507_;
                        v___y_1487_ = v_finSeq_x3f_1509_;
                        v___y_1488_ = v___y_1515_;
                        v___y_1489_ = v___y_1514_;
                        v___y_1490_ = v___y_1512_;
                        v___y_1491_ = v___x_1517_;
                        v___y_1492_ = v___y_1513_;
                        v___y_1493_ = v___x_1520_;
                        state = 15;
                        continue;
                    } else {
                        if lean_obj_tag(v_finSeq_x3f_1509_) == 0 {
                            v___y_1483_ = v___y_1511_;
                            v___y_1484_ = v___y_1510_;
                            v___y_1485_ = v___y_1516_;
                            v___y_1486_ = v___f_1507_;
                            v___y_1487_ = v_finSeq_x3f_1509_;
                            v___y_1488_ = v___y_1515_;
                            v___y_1489_ = v___y_1514_;
                            v___y_1490_ = v___y_1512_;
                            v___y_1491_ = v___x_1517_;
                            v___y_1492_ = v___y_1513_;
                            v___y_1493_ = v___x_1520_;
                            state = 15;
                            continue;
                        } else {
                            v___y_1443_ = v_finSeq_x3f_1509_;
                            v___y_1444_ = v___f_1507_;
                            v___y_1445_ = v___x_1517_;
                            v___y_1446_ = v___y_1510_;
                            v___y_1447_ = v___y_1511_;
                            v___y_1448_ = v___y_1512_;
                            v___y_1449_ = v___y_1513_;
                            v___y_1450_ = v___y_1514_;
                            v___y_1451_ = v___y_1515_;
                            v___y_1452_ = v___y_1516_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_finSeq_x3f_1509_);
                    lean_dec_ref(v___f_1507_);
                    lean_dec(v_val_1437_);
                    lean_dec_ref(v_dec_1333_);
                    lean_dec(v_stx_1332_);
                    v_a_1521_ = lean_ctor_get(v___x_1519_, 0);
                    v_isSharedCheck_1528_ = (!lean_is_exclusive(v___x_1519_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1523_ = v___x_1519_;
                        v_isShared_1524_ = v_isSharedCheck_1528_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_1521_);
                        lean_dec(v___x_1519_);
                        v___x_1523_ = lean_box(0);
                        v_isShared_1524_ = v_isSharedCheck_1528_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_1524_ == 0 {
                    v___x_1526_ = v___x_1523_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1526_;
            }
            21 => {
                v_finSeq_x3f_1509_ = v___x_1540_;
                v___y_1510_ = v_a_1334_;
                v___y_1511_ = v_a_1335_;
                v___y_1512_ = v_a_1336_;
                v___y_1513_ = v_a_1337_;
                v___y_1514_ = v_a_1338_;
                v___y_1515_ = v_a_1339_;
                v___y_1516_ = v_a_1340_;
                state = 18;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoTry___boxed(
    mut v_stx_1544_: *mut LeanObject,
    mut v_dec_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
    mut v_a_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1554_: *mut LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Lean_Elab_Do_elabDoTry(
        v_stx_1544_,
        v_dec_1545_,
        v_a_1546_,
        v_a_1547_,
        v_a_1548_,
        v_a_1549_,
        v_a_1550_,
        v_a_1551_,
        v_a_1552_,
    );
    lean_dec(v_a_1552_);
    lean_dec_ref(v_a_1551_);
    lean_dec(v_a_1550_);
    lean_dec_ref(v_a_1549_);
    lean_dec(v_a_1548_);
    lean_dec_ref(v_a_1547_);
    lean_dec_ref(v_a_1546_);
    return v_res_1554_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(
    mut v_00_u03b1_1555_: *mut LeanObject,
    mut v_msg_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
    mut v___y_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v___x_1565_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(
        v_msg_1556_,
        v___y_1560_,
        v___y_1561_,
        v___y_1562_,
        v___y_1563_,
    );
    return v___x_1565_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___boxed(
    mut v_00_u03b1_1566_: *mut LeanObject,
    mut v_msg_1567_: *mut LeanObject,
    mut v___y_1568_: *mut LeanObject,
    mut v___y_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1576_: *mut LeanObject = core::ptr::null_mut();
    v_res_1576_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(
        v_00_u03b1_1566_,
        v_msg_1567_,
        v___y_1568_,
        v___y_1569_,
        v___y_1570_,
        v___y_1571_,
        v___y_1572_,
        v___y_1573_,
        v___y_1574_,
    );
    lean_dec(v___y_1574_);
    lean_dec_ref(v___y_1573_);
    lean_dec(v___y_1572_);
    lean_dec_ref(v___y_1571_);
    lean_dec(v___y_1570_);
    lean_dec_ref(v___y_1569_);
    lean_dec_ref(v___y_1568_);
    return v_res_1576_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1()
-> *mut LeanObject {
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1586_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_1587_ = l_Lean_Elab_Do_elabDoTry___closed__1;
    v___x_1588_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3;
    v___x_1589_ = lean_alloc_closure(
        l_Lean_Elab_Do_elabDoTry___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1590_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1586_,
        v___x_1587_,
        v___x_1588_,
        v___x_1589_,
    );
    return v___x_1590_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___boxed(
    mut v_a_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1592_: *mut LeanObject = core::ptr::null_mut();
    v_res_1592_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
    return v_res_1592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_TryCatch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Do_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
}
