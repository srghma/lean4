// Lean compiler output
// Module: Lean.Elab.BuiltinDo.If
// Imports: Lean.Elab.Do.Basic Lean.Parser.Do Lean.Elab.BuiltinDo.Basic
use crate::r#gen::Init::Data::Array::Basic::{l_Array_reverse___redArg, l_Array_zip___redArg};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node4,
    l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_Syntax_node8,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::BuiltinDo::Basic::{
    initialize_Lean_Elab_BuiltinDo_Basic, runtime_initialize_Lean_Elab_BuiltinDo_Basic,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_DoElemCont_withDuplicableCont,
    l_Lean_Elab_Do_doElabToSyntax___redArg, l_Lean_Elab_Do_doElemElabAttribute,
    l_Lean_Elab_Do_elabDoSeq, l_Lean_Elab_Do_elabDoSeq___boxed, l_Lean_Elab_Do_mkMonadApp,
    runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Do::InferControlInfo::{
    l_Lean_Elab_Do_ControlInfo_alternative, l_Lean_Elab_Do_inferControlInfoSeq,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_elabTermEnsuringType;
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_array_push;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 73, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value) as *mut crate::leanh::LeanObject,6082561497774213 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 73, 102, 76, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value) as *mut crate::leanh::LeanObject,847678388818273205 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 73, 102, 80, 114, 111, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value) as *mut crate::leanh::LeanObject,10892447550847226679 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 73, 102, 76, 101, 116, 80, 117, 114, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value) as *mut crate::leanh::LeanObject,13802184170640645406 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 73, 102, 76, 101, 116, 66, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value) as *mut crate::leanh::LeanObject,14346931504061664251 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 77, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value) as *mut crate::leanh::LeanObject,4365236509002904093 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value) as *mut crate::leanh::LeanObject,9383794970646754147 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 101, 115, 116, 101, 100, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value) as *mut crate::leanh::LeanObject,14598754423419706227 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value) as *mut crate::leanh::LeanObject,13242179749370575553 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value) as *mut crate::leanh::LeanObject,3326968124746134365 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value) as *mut crate::leanh::LeanObject,940684074193935882 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,2214559063752339918 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoIf___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            73, 110, 116, 101, 114, 110, 97, 108, 83, 121, 110, 116, 97, 120, 0,
        ],
    };
static mut l_Lean_Elab_Do_expandDoIf___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoIf___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [100, 111, 83, 107, 105, 112, 0],
    };
static mut l_Lean_Elab_Do_expandDoIf___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3428822669065651317 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_expandDoIf___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__1_value)
                as *mut crate::leanh::LeanObject,
            12861224375759052157 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoIf___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoIf___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 107, 105, 112, 0],
    };
static mut l_Lean_Elab_Do_expandDoIf___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoIf___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 73, 102, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value) as *mut crate::leanh::LeanObject,7151595208354922900 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value: crate::leanh::LeanStringObject<113> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 113, m_capacity: 113, m_length: 112, m_data: [73, 102, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 32, 105, 115, 32, 97, 32, 96, 100, 111, 73, 102, 96, 44, 32, 114, 101, 116, 117, 114, 110, 32, 97, 110, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 96, 100, 111, 73, 102, 96, 32, 116, 104, 97, 116, 32, 104, 97, 115, 32, 97, 110, 32, 96, 101, 108, 115, 101, 96, 32, 98, 117, 116, 32, 110, 111, 32, 96, 101, 108, 115, 101, 32, 105, 102, 96, 115, 32, 111, 114, 10, 96, 105, 102, 32, 108, 101, 116, 96, 115, 46, 10, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,14296711813398647265 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [101, 108, 115, 101, 32, 98, 114, 97, 110, 99, 104, 32, 111, 102, 32, 105, 102, 32, 119, 105, 116, 104, 32, 99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 123, 99, 111, 110, 100, 125, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        116, 104, 101, 110, 32, 98, 114, 97, 110, 99, 104, 32, 111, 102, 32, 105, 102, 32, 119,
        105, 116, 104, 32, 99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 123, 99, 111, 110, 100,
        125, 0,
    ],
};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 101, 114, 109, 68, 101, 112, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12532511233276993215 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value) as *mut crate::leanh::LeanObject,13771926289831477797 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 68, 111, 73, 102, 0]};
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value) as *mut crate::leanh::LeanObject,10556884564635431559 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(
    mut v___x_1321_: u8,
    mut v_____do__lift_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1322_, v___x_1321_);
    v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1325_);
    crate::leanh::lean_ctor_set(v___x_1326_, 1, v___y_1324_);
    return v___x_1326_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0___boxed(
    mut v___x_1327_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34972__boxed_1331_: u8 = 0;
    let mut v_res_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34972__boxed_1331_ = (crate::leanh::lean_unbox(v___x_1327_) as u8);
    v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_34972__boxed_1331_, v_____do__lift_1328_, v___y_1329_, v___y_1330_);
    crate::leanh::lean_dec_ref(v___y_1329_);
    crate::leanh::lean_dec(v_____do__lift_1328_);
    return v_res_1332_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1359_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1359_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(
    mut v___x_1427_: u8,
    mut v_as_1428_: *mut crate::leanh::LeanObject,
    mut v_sz_1429_: usize,
    mut v_i_1430_: usize,
    mut v_b_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v_fst_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_ref_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_ref_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1564_: u8 = 0;
    let mut v_ref_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v___x_1613_: u8 = 0;
    let mut v_ref_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1442_ = lean_usize_dec_lt(v_i_1430_, v_sz_1429_);
                if v___x_1442_ == 0 {
                    v___x_1443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1443_, 0, v_b_1431_);
                    crate::leanh::lean_ctor_set(v___x_1443_, 1, v___y_1433_);
                    return v___x_1443_;
                } else {
                    v_a_1444_ = lean_array_uget(v_as_1428_, v_i_1430_);
                    v_fst_1445_ = crate::leanh::lean_ctor_get(v_a_1444_, 0);
                    v_snd_1446_ = crate::leanh::lean_ctor_get(v_a_1444_, 1);
                    v_isSharedCheck_1636_ = (!crate::leanh::lean_is_exclusive(v_a_1444_)) as u8;
                    if v_isSharedCheck_1636_ == 0 {
                        v___x_1448_ = v_a_1444_;
                        v_isShared_1449_ = v_isSharedCheck_1636_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1446_);
                        crate::leanh::lean_inc(v_fst_1445_);
                        crate::leanh::lean_dec(v_a_1444_);
                        v___x_1448_ = crate::leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1636_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1437_ = crate::leanh::lean_box((v___x_1427_) as usize);
                v___x_1438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1438_, 0, v_e_1435_);
                crate::leanh::lean_ctor_set(v___x_1438_, 1, v___x_1437_);
                v___x_1439_ = 1usize;
                v___x_1440_ = lean_usize_add(v_i_1430_, v___x_1439_);
                v_i_1430_ = v___x_1440_;
                v_b_1431_ = v___x_1438_;
                v___y_1433_ = v___y_1436_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_1450_ = crate::leanh::lean_ctor_get(v_b_1431_, 0);
                v_snd_1451_ = crate::leanh::lean_ctor_get(v_b_1431_, 1);
                v_isSharedCheck_1635_ = (!crate::leanh::lean_is_exclusive(v_b_1431_)) as u8;
                if v_isSharedCheck_1635_ == 0 {
                    v___x_1453_ = v_b_1431_;
                    v_isShared_1454_ = v_isSharedCheck_1635_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1451_);
                    crate::leanh::lean_inc(v_fst_1450_);
                    crate::leanh::lean_dec(v_b_1431_);
                    v___x_1453_ = crate::leanh::lean_box(0);
                    v_isShared_1454_ = v_isSharedCheck_1635_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4;
                v___x_1456_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1457_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1613_ = (crate::leanh::lean_unbox(v_snd_1451_) as u8);
                crate::leanh::lean_dec(v_snd_1451_);
                if v___x_1613_ == 0 {
                    v_ref_1614_ = crate::leanh::lean_ctor_get(v___y_1432_, 5);
                    v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_1427_, v_ref_1614_, v___y_1432_, v___y_1433_);
                    if crate::leanh::lean_obj_tag(v___x_1615_) == 0 {
                        v_a_1616_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                        crate::leanh::lean_inc_n(v_a_1616_, 4);
                        v_a_1617_ = crate::leanh::lean_ctor_get(v___x_1615_, 1);
                        crate::leanh::lean_inc(v_a_1617_);
                        crate::leanh::lean_dec_ref_known(v___x_1615_, 2);
                        v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38;
                        v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                        v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40;
                        v___x_1621_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                        v___x_1622_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1622_, 0, v_a_1616_);
                        crate::leanh::lean_ctor_set(v___x_1622_, 1, v___x_1619_);
                        crate::leanh::lean_ctor_set(v___x_1622_, 2, v___x_1621_);
                        v___x_1623_ =
                            l_Lean_Syntax_node2(v_a_1616_, v___x_1620_, v_fst_1450_, v___x_1622_);
                        v___x_1624_ = l_Lean_Syntax_node1(v_a_1616_, v___x_1619_, v___x_1623_);
                        v___x_1625_ = l_Lean_Syntax_node1(v_a_1616_, v___x_1618_, v___x_1624_);
                        v_e_1459_ = v___x_1625_;
                        v___y_1460_ = v___y_1432_;
                        v___y_1461_ = v_a_1617_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1453_);
                        crate::leanh::lean_dec(v_fst_1450_);
                        crate::leanh::lean_del_object(v___x_1448_);
                        crate::leanh::lean_dec(v_snd_1446_);
                        crate::leanh::lean_dec(v_fst_1445_);
                        v_a_1626_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                        v_a_1627_ = crate::leanh::lean_ctor_get(v___x_1615_, 1);
                        v_isSharedCheck_1634_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1615_)) as u8;
                        if v_isSharedCheck_1634_ == 0 {
                            v___x_1629_ = v___x_1615_;
                            v_isShared_1630_ = v_isSharedCheck_1634_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1627_);
                            crate::leanh::lean_inc(v_a_1626_);
                            crate::leanh::lean_dec(v___x_1615_);
                            v___x_1629_ = crate::leanh::lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1634_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    v_e_1459_ = v_fst_1450_;
                    v___y_1460_ = v___y_1432_;
                    v___y_1461_ = v___y_1433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6;
                crate::leanh::lean_inc(v_fst_1445_);
                v___x_1463_ = l_Lean_Syntax_isOfKind(v_fst_1445_, v___x_1462_);
                if v___x_1463_ == 0 {
                    v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8;
                    crate::leanh::lean_inc(v_fst_1445_);
                    v___x_1465_ = l_Lean_Syntax_isOfKind(v_fst_1445_, v___x_1464_);
                    if v___x_1465_ == 0 {
                        crate::leanh::lean_dec(v_e_1459_);
                        crate::leanh::lean_del_object(v___x_1453_);
                        crate::leanh::lean_del_object(v___x_1448_);
                        crate::leanh::lean_dec(v_snd_1446_);
                        crate::leanh::lean_dec(v_fst_1445_);
                        v___x_1466_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1461_);
                        if crate::leanh::lean_obj_tag(v___x_1466_) == 0 {
                            v_a_1467_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                            crate::leanh::lean_inc(v_a_1467_);
                            v_a_1468_ = crate::leanh::lean_ctor_get(v___x_1466_, 1);
                            crate::leanh::lean_inc(v_a_1468_);
                            crate::leanh::lean_dec_ref_known(v___x_1466_, 2);
                            v_e_1435_ = v_a_1467_;
                            v___y_1436_ = v_a_1468_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1469_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                            v_a_1470_ = crate::leanh::lean_ctor_get(v___x_1466_, 1);
                            v_isSharedCheck_1477_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1466_)) as u8;
                            if v_isSharedCheck_1477_ == 0 {
                                v___x_1472_ = v___x_1466_;
                                v_isShared_1473_ = v_isSharedCheck_1477_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1470_);
                                crate::leanh::lean_inc(v_a_1469_);
                                crate::leanh::lean_dec(v___x_1466_);
                                v___x_1472_ = crate::leanh::lean_box(0);
                                v_isShared_1473_ = v_isSharedCheck_1477_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_ref_1478_ = crate::leanh::lean_ctor_get(v___y_1460_, 5);
                        v___x_1479_ = l_Lean_SourceInfo_fromRef(v_ref_1478_, v___x_1427_);
                        v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9;
                        crate::leanh::lean_inc(v___x_1479_);
                        if v_isShared_1454_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1453_, 2);
                            crate::leanh::lean_ctor_set(v___x_1453_, 1, v___x_1480_);
                            crate::leanh::lean_ctor_set(v___x_1453_, 0, v___x_1479_);
                            v___x_1482_ = v___x_1453_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1494_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1479_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1480_);
                            v___x_1482_ = v_reuseFailAlloc_1494_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_1495_ = l_Lean_Syntax_getArg(v_fst_1445_, v___x_1456_);
                    v___x_1496_ = l_Lean_Syntax_getArg(v_fst_1445_, v___x_1457_);
                    crate::leanh::lean_dec(v_fst_1445_);
                    v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16;
                    crate::leanh::lean_inc(v___x_1496_);
                    v___x_1498_ = l_Lean_Syntax_isOfKind(v___x_1496_, v___x_1497_);
                    if v___x_1498_ == 0 {
                        v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18;
                        crate::leanh::lean_inc(v___x_1496_);
                        v___x_1500_ = l_Lean_Syntax_isOfKind(v___x_1496_, v___x_1499_);
                        if v___x_1500_ == 0 {
                            crate::leanh::lean_dec(v___x_1496_);
                            crate::leanh::lean_dec(v___x_1495_);
                            crate::leanh::lean_dec(v_e_1459_);
                            crate::leanh::lean_del_object(v___x_1453_);
                            crate::leanh::lean_del_object(v___x_1448_);
                            crate::leanh::lean_dec(v_snd_1446_);
                            v___x_1501_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1461_);
                            if crate::leanh::lean_obj_tag(v___x_1501_) == 0 {
                                v_a_1502_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                                crate::leanh::lean_inc(v_a_1502_);
                                v_a_1503_ = crate::leanh::lean_ctor_get(v___x_1501_, 1);
                                crate::leanh::lean_inc(v_a_1503_);
                                crate::leanh::lean_dec_ref_known(v___x_1501_, 2);
                                v_e_1435_ = v_a_1502_;
                                v___y_1436_ = v_a_1503_;
                                state = 1;
                                continue;
                            } else {
                                v_a_1504_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                                v_a_1505_ = crate::leanh::lean_ctor_get(v___x_1501_, 1);
                                v_isSharedCheck_1512_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1501_)) as u8;
                                if v_isSharedCheck_1512_ == 0 {
                                    v___x_1507_ = v___x_1501_;
                                    v_isShared_1508_ = v_isSharedCheck_1512_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1505_);
                                    crate::leanh::lean_inc(v_a_1504_);
                                    crate::leanh::lean_dec(v___x_1501_);
                                    v___x_1507_ = crate::leanh::lean_box(0);
                                    v_isShared_1508_ = v_isSharedCheck_1512_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            v_ref_1513_ = crate::leanh::lean_ctor_get(v___y_1460_, 5);
                            v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_1427_, v_ref_1513_, v___y_1460_, v___y_1461_);
                            if crate::leanh::lean_obj_tag(v___x_1514_) == 0 {
                                v_a_1515_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                                crate::leanh::lean_inc_n(v_a_1515_, 2);
                                v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1514_, 1);
                                crate::leanh::lean_inc(v_a_1516_);
                                crate::leanh::lean_dec_ref_known(v___x_1514_, 2);
                                v___x_1517_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1456_);
                                crate::leanh::lean_dec(v___x_1496_);
                                v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20;
                                v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21;
                                if v_isShared_1454_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_1453_, 2);
                                    crate::leanh::lean_ctor_set(v___x_1453_, 1, v___x_1519_);
                                    crate::leanh::lean_ctor_set(v___x_1453_, 0, v_a_1515_);
                                    v___x_1521_ = v___x_1453_;
                                    state = 11;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1555_ =
                                        crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1555_,
                                        0,
                                        v_a_1515_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1555_,
                                        1,
                                        v___x_1519_,
                                    );
                                    v___x_1521_ = v_reuseFailAlloc_1555_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1496_);
                                crate::leanh::lean_dec(v___x_1495_);
                                crate::leanh::lean_dec(v_e_1459_);
                                crate::leanh::lean_del_object(v___x_1453_);
                                crate::leanh::lean_del_object(v___x_1448_);
                                crate::leanh::lean_dec(v_snd_1446_);
                                v_a_1556_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                                v_a_1557_ = crate::leanh::lean_ctor_get(v___x_1514_, 1);
                                v_isSharedCheck_1564_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1514_)) as u8;
                                if v_isSharedCheck_1564_ == 0 {
                                    v___x_1559_ = v___x_1514_;
                                    v_isShared_1560_ = v_isSharedCheck_1564_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1557_);
                                    crate::leanh::lean_inc(v_a_1556_);
                                    crate::leanh::lean_dec(v___x_1514_);
                                    v___x_1559_ = crate::leanh::lean_box(0);
                                    v_isShared_1560_ = v_isSharedCheck_1564_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_ref_1565_ = crate::leanh::lean_ctor_get(v___y_1460_, 5);
                        v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_1427_, v_ref_1565_, v___y_1460_, v___y_1461_);
                        if crate::leanh::lean_obj_tag(v___x_1566_) == 0 {
                            v_a_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                            crate::leanh::lean_inc_n(v_a_1567_, 2);
                            v_a_1568_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                            crate::leanh::lean_inc(v_a_1568_);
                            crate::leanh::lean_dec_ref_known(v___x_1566_, 2);
                            v___x_1569_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1456_);
                            crate::leanh::lean_dec(v___x_1496_);
                            v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20;
                            v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21;
                            if v_isShared_1454_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1453_, 2);
                                crate::leanh::lean_ctor_set(v___x_1453_, 1, v___x_1571_);
                                crate::leanh::lean_ctor_set(v___x_1453_, 0, v_a_1567_);
                                v___x_1573_ = v___x_1453_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_1603_ =
                                    crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1567_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1571_);
                                v___x_1573_ = v_reuseFailAlloc_1603_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1496_);
                            crate::leanh::lean_dec(v___x_1495_);
                            crate::leanh::lean_dec(v_e_1459_);
                            crate::leanh::lean_del_object(v___x_1453_);
                            crate::leanh::lean_del_object(v___x_1448_);
                            crate::leanh::lean_dec(v_snd_1446_);
                            v_a_1604_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                            v_a_1605_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                            v_isSharedCheck_1612_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                            if v_isSharedCheck_1612_ == 0 {
                                v___x_1607_ = v___x_1566_;
                                v_isShared_1608_ = v_isSharedCheck_1612_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1605_);
                                crate::leanh::lean_inc(v_a_1604_);
                                crate::leanh::lean_dec(v___x_1566_);
                                v___x_1607_ = crate::leanh::lean_box(0);
                                v_isShared_1608_ = v_isSharedCheck_1612_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                if v_isShared_1473_ == 0 {
                    v___x_1475_ = v___x_1472_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1470_);
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1475_;
            }
            7 => {
                v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10;
                crate::leanh::lean_inc(v___x_1479_);
                if v_isShared_1449_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1448_, 2);
                    crate::leanh::lean_ctor_set(v___x_1448_, 1, v___x_1483_);
                    crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1479_);
                    v___x_1485_ = v___x_1448_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1483_);
                    v___x_1485_ = v_reuseFailAlloc_1493_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_1487_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                crate::leanh::lean_inc_n(v___x_1479_, 3);
                v___x_1488_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1488_, 0, v___x_1479_);
                crate::leanh::lean_ctor_set(v___x_1488_, 1, v___x_1486_);
                crate::leanh::lean_ctor_set(v___x_1488_, 2, v___x_1487_);
                v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14;
                v___x_1490_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1490_, 0, v___x_1479_);
                crate::leanh::lean_ctor_set(v___x_1490_, 1, v___x_1489_);
                v___x_1491_ = l_Lean_Syntax_node2(v___x_1479_, v___x_1486_, v___x_1490_, v_e_1459_);
                v___x_1492_ = l_Lean_Syntax_node6(
                    v___x_1479_,
                    v___x_1455_,
                    v___x_1482_,
                    v_fst_1445_,
                    v___x_1485_,
                    v_snd_1446_,
                    v___x_1488_,
                    v___x_1491_,
                );
                v_e_1435_ = v___x_1492_;
                v___y_1436_ = v___y_1461_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_1508_ == 0 {
                    v___x_1510_ = v___x_1507_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_a_1505_);
                    v___x_1510_ = v_reuseFailAlloc_1511_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1510_;
            }
            11 => {
                v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_1523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                crate::leanh::lean_inc_n(v_a_1515_, 2);
                v___x_1524_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1524_, 0, v_a_1515_);
                crate::leanh::lean_ctor_set(v___x_1524_, 1, v___x_1522_);
                crate::leanh::lean_ctor_set(v___x_1524_, 2, v___x_1523_);
                v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23;
                v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25;
                v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26;
                if v_isShared_1449_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1448_, 2);
                    crate::leanh::lean_ctor_set(v___x_1448_, 1, v___x_1527_);
                    crate::leanh::lean_ctor_set(v___x_1448_, 0, v_a_1515_);
                    v___x_1529_ = v___x_1448_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1554_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1554_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_n(v_a_1515_, 16);
                v___x_1530_ = l_Lean_Syntax_node2(v_a_1515_, v___x_1526_, v___x_1529_, v___x_1517_);
                crate::leanh::lean_inc_ref_n(v___x_1524_, 3);
                v___x_1531_ = l_Lean_Syntax_node2(v_a_1515_, v___x_1525_, v___x_1524_, v___x_1530_);
                v___x_1532_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1522_, v___x_1531_);
                v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27;
                v___x_1534_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1534_, 0, v_a_1515_);
                crate::leanh::lean_ctor_set(v___x_1534_, 1, v___x_1533_);
                v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29;
                v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31;
                v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32;
                v___x_1538_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1538_, 0, v_a_1515_);
                crate::leanh::lean_ctor_set(v___x_1538_, 1, v___x_1537_);
                v___x_1539_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1522_, v___x_1495_);
                v___x_1540_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1522_, v___x_1539_);
                v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33;
                v___x_1542_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1542_, 0, v_a_1515_);
                crate::leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
                crate::leanh::lean_inc_ref(v___x_1542_);
                crate::leanh::lean_inc_ref(v___x_1538_);
                v___x_1543_ = l_Lean_Syntax_node4(
                    v_a_1515_,
                    v___x_1536_,
                    v___x_1538_,
                    v___x_1540_,
                    v___x_1542_,
                    v_snd_1446_,
                );
                v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35;
                v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36;
                v___x_1546_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1546_, 0, v_a_1515_);
                crate::leanh::lean_ctor_set(v___x_1546_, 1, v___x_1545_);
                v___x_1547_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1544_, v___x_1546_);
                v___x_1548_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1522_, v___x_1547_);
                v___x_1549_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1522_, v___x_1548_);
                v___x_1550_ = l_Lean_Syntax_node4(
                    v_a_1515_,
                    v___x_1536_,
                    v___x_1538_,
                    v___x_1549_,
                    v___x_1542_,
                    v_e_1459_,
                );
                v___x_1551_ = l_Lean_Syntax_node2(v_a_1515_, v___x_1522_, v___x_1543_, v___x_1550_);
                v___x_1552_ = l_Lean_Syntax_node1(v_a_1515_, v___x_1535_, v___x_1551_);
                v___x_1553_ = l_Lean_Syntax_node7(
                    v_a_1515_,
                    v___x_1518_,
                    v___x_1521_,
                    v___x_1524_,
                    v___x_1524_,
                    v___x_1524_,
                    v___x_1532_,
                    v___x_1534_,
                    v___x_1552_,
                );
                v_e_1435_ = v___x_1553_;
                v___y_1436_ = v_a_1516_;
                state = 1;
                continue;
            }
            13 => {
                if v_isShared_1560_ == 0 {
                    v___x_1562_ = v___x_1559_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1563_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_a_1557_);
                    v___x_1562_ = v_reuseFailAlloc_1563_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1562_;
            }
            15 => {
                v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_1575_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                crate::leanh::lean_inc_n(v_a_1567_, 4);
                v___x_1576_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1576_, 0, v_a_1567_);
                crate::leanh::lean_ctor_set(v___x_1576_, 1, v___x_1574_);
                crate::leanh::lean_ctor_set(v___x_1576_, 2, v___x_1575_);
                v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23;
                crate::leanh::lean_inc_ref(v___x_1576_);
                v___x_1578_ = l_Lean_Syntax_node2(v_a_1567_, v___x_1577_, v___x_1576_, v___x_1569_);
                v___x_1579_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1574_, v___x_1578_);
                v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27;
                if v_isShared_1449_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1448_, 2);
                    crate::leanh::lean_ctor_set(v___x_1448_, 1, v___x_1580_);
                    crate::leanh::lean_ctor_set(v___x_1448_, 0, v_a_1567_);
                    v___x_1582_ = v___x_1448_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1580_);
                    v___x_1582_ = v_reuseFailAlloc_1602_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29;
                v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31;
                v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32;
                crate::leanh::lean_inc_n(v_a_1567_, 12);
                v___x_1586_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1586_, 0, v_a_1567_);
                crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1585_);
                v___x_1587_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1574_, v___x_1495_);
                v___x_1588_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1574_, v___x_1587_);
                v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33;
                v___x_1590_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1590_, 0, v_a_1567_);
                crate::leanh::lean_ctor_set(v___x_1590_, 1, v___x_1589_);
                crate::leanh::lean_inc_ref(v___x_1590_);
                crate::leanh::lean_inc_ref(v___x_1586_);
                v___x_1591_ = l_Lean_Syntax_node4(
                    v_a_1567_,
                    v___x_1584_,
                    v___x_1586_,
                    v___x_1588_,
                    v___x_1590_,
                    v_snd_1446_,
                );
                v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35;
                v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36;
                v___x_1594_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1594_, 0, v_a_1567_);
                crate::leanh::lean_ctor_set(v___x_1594_, 1, v___x_1593_);
                v___x_1595_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1592_, v___x_1594_);
                v___x_1596_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1574_, v___x_1595_);
                v___x_1597_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1574_, v___x_1596_);
                v___x_1598_ = l_Lean_Syntax_node4(
                    v_a_1567_,
                    v___x_1584_,
                    v___x_1586_,
                    v___x_1597_,
                    v___x_1590_,
                    v_e_1459_,
                );
                v___x_1599_ = l_Lean_Syntax_node2(v_a_1567_, v___x_1574_, v___x_1591_, v___x_1598_);
                v___x_1600_ = l_Lean_Syntax_node1(v_a_1567_, v___x_1583_, v___x_1599_);
                crate::leanh::lean_inc_ref_n(v___x_1576_, 2);
                v___x_1601_ = l_Lean_Syntax_node7(
                    v_a_1567_,
                    v___x_1570_,
                    v___x_1573_,
                    v___x_1576_,
                    v___x_1576_,
                    v___x_1576_,
                    v___x_1579_,
                    v___x_1582_,
                    v___x_1600_,
                );
                v_e_1435_ = v___x_1601_;
                v___y_1436_ = v_a_1568_;
                state = 1;
                continue;
            }
            17 => {
                if v_isShared_1608_ == 0 {
                    v___x_1610_ = v___x_1607_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1605_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1610_;
            }
            19 => {
                if v_isShared_1630_ == 0 {
                    v___x_1632_ = v___x_1629_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1633_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_a_1627_);
                    v___x_1632_ = v_reuseFailAlloc_1633_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(
    mut v___x_1637_: *mut crate::leanh::LeanObject,
    mut v_as_1638_: *mut crate::leanh::LeanObject,
    mut v_sz_1639_: *mut crate::leanh::LeanObject,
    mut v_i_1640_: *mut crate::leanh::LeanObject,
    mut v_b_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_35223__boxed_1644_: u8 = 0;
    let mut v_sz_boxed_1645_: usize = 0;
    let mut v_i_boxed_1646_: usize = 0;
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_35223__boxed_1644_ = (crate::leanh::lean_unbox(v___x_1637_) as u8);
    v_sz_boxed_1645_ = crate::leanh::lean_unbox_usize(v_sz_1639_);
    crate::leanh::lean_dec(v_sz_1639_);
    v_i_boxed_1646_ = crate::leanh::lean_unbox_usize(v_i_1640_);
    crate::leanh::lean_dec(v_i_1640_);
    v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_35223__boxed_1644_, v_as_1638_, v_sz_boxed_1645_, v_i_boxed_1646_, v_b_1641_, v___y_1642_, v___y_1643_);
    crate::leanh::lean_dec_ref(v___y_1642_);
    crate::leanh::lean_dec_ref(v_as_1638_);
    return v_res_1647_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(
    mut v_____do__lift_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = 0;
    v___x_1652_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1648_, v___x_1651_);
    v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1652_);
    crate::leanh::lean_ctor_set(v___x_1653_, 1, v___y_1650_);
    return v___x_1653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(
    mut v_____do__lift_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_____do__lift_1654_, v___y_1655_, v___y_1656_);
    crate::leanh::lean_dec_ref(v___y_1655_);
    crate::leanh::lean_dec(v_____do__lift_1654_);
    return v_res_1657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(
    mut v_as_1658_: *mut crate::leanh::LeanObject,
    mut v_sz_1659_: usize,
    mut v_i_1660_: usize,
    mut v_b_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: usize = 0;
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v_fst_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1685_: u8 = 0;
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1704_: u8 = 0;
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_ref_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_ref_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_ref_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1839_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v___x_1844_: u8 = 0;
    let mut v_ref_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1861_: u8 = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1673_ = lean_usize_dec_lt(v_i_1660_, v_sz_1659_);
                if v___x_1673_ == 0 {
                    v___x_1674_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1674_, 0, v_b_1661_);
                    crate::leanh::lean_ctor_set(v___x_1674_, 1, v___y_1663_);
                    return v___x_1674_;
                } else {
                    v_a_1675_ = lean_array_uget(v_as_1658_, v_i_1660_);
                    v_fst_1676_ = crate::leanh::lean_ctor_get(v_a_1675_, 0);
                    v_snd_1677_ = crate::leanh::lean_ctor_get(v_a_1675_, 1);
                    v_isSharedCheck_1867_ = (!crate::leanh::lean_is_exclusive(v_a_1675_)) as u8;
                    if v_isSharedCheck_1867_ == 0 {
                        v___x_1679_ = v_a_1675_;
                        v_isShared_1680_ = v_isSharedCheck_1867_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1677_);
                        crate::leanh::lean_inc(v_fst_1676_);
                        crate::leanh::lean_dec(v_a_1675_);
                        v___x_1679_ = crate::leanh::lean_box(0);
                        v_isShared_1680_ = v_isSharedCheck_1867_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1667_ = 0;
                v___x_1668_ = crate::leanh::lean_box((v___x_1667_) as usize);
                v___x_1669_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1669_, 0, v_e_1665_);
                crate::leanh::lean_ctor_set(v___x_1669_, 1, v___x_1668_);
                v___x_1670_ = 1usize;
                v___x_1671_ = lean_usize_add(v_i_1660_, v___x_1670_);
                v_i_1660_ = v___x_1671_;
                v_b_1661_ = v___x_1669_;
                v___y_1663_ = v___y_1666_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_1681_ = crate::leanh::lean_ctor_get(v_b_1661_, 0);
                v_snd_1682_ = crate::leanh::lean_ctor_get(v_b_1661_, 1);
                v_isSharedCheck_1866_ = (!crate::leanh::lean_is_exclusive(v_b_1661_)) as u8;
                if v_isSharedCheck_1866_ == 0 {
                    v___x_1684_ = v_b_1661_;
                    v_isShared_1685_ = v_isSharedCheck_1866_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1682_);
                    crate::leanh::lean_inc(v_fst_1681_);
                    crate::leanh::lean_dec(v_b_1661_);
                    v___x_1684_ = crate::leanh::lean_box(0);
                    v_isShared_1685_ = v_isSharedCheck_1866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4;
                v___x_1687_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1688_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1844_ = (crate::leanh::lean_unbox(v_snd_1682_) as u8);
                crate::leanh::lean_dec(v_snd_1682_);
                if v___x_1844_ == 0 {
                    v_ref_1845_ = crate::leanh::lean_ctor_get(v___y_1662_, 5);
                    v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_1845_, v___y_1662_, v___y_1663_);
                    if crate::leanh::lean_obj_tag(v___x_1846_) == 0 {
                        v_a_1847_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                        crate::leanh::lean_inc_n(v_a_1847_, 4);
                        v_a_1848_ = crate::leanh::lean_ctor_get(v___x_1846_, 1);
                        crate::leanh::lean_inc(v_a_1848_);
                        crate::leanh::lean_dec_ref_known(v___x_1846_, 2);
                        v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38;
                        v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                        v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40;
                        v___x_1852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                        v___x_1853_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1853_, 0, v_a_1847_);
                        crate::leanh::lean_ctor_set(v___x_1853_, 1, v___x_1850_);
                        crate::leanh::lean_ctor_set(v___x_1853_, 2, v___x_1852_);
                        v___x_1854_ =
                            l_Lean_Syntax_node2(v_a_1847_, v___x_1851_, v_fst_1681_, v___x_1853_);
                        v___x_1855_ = l_Lean_Syntax_node1(v_a_1847_, v___x_1850_, v___x_1854_);
                        v___x_1856_ = l_Lean_Syntax_node1(v_a_1847_, v___x_1849_, v___x_1855_);
                        v_e_1690_ = v___x_1856_;
                        v___y_1691_ = v___y_1662_;
                        v___y_1692_ = v_a_1848_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1684_);
                        crate::leanh::lean_dec(v_fst_1681_);
                        crate::leanh::lean_del_object(v___x_1679_);
                        crate::leanh::lean_dec(v_snd_1677_);
                        crate::leanh::lean_dec(v_fst_1676_);
                        v_a_1857_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                        v_a_1858_ = crate::leanh::lean_ctor_get(v___x_1846_, 1);
                        v_isSharedCheck_1865_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1846_)) as u8;
                        if v_isSharedCheck_1865_ == 0 {
                            v___x_1860_ = v___x_1846_;
                            v_isShared_1861_ = v_isSharedCheck_1865_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1858_);
                            crate::leanh::lean_inc(v_a_1857_);
                            crate::leanh::lean_dec(v___x_1846_);
                            v___x_1860_ = crate::leanh::lean_box(0);
                            v_isShared_1861_ = v_isSharedCheck_1865_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    v_e_1690_ = v_fst_1681_;
                    v___y_1691_ = v___y_1662_;
                    v___y_1692_ = v___y_1663_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6;
                crate::leanh::lean_inc(v_fst_1676_);
                v___x_1694_ = l_Lean_Syntax_isOfKind(v_fst_1676_, v___x_1693_);
                if v___x_1694_ == 0 {
                    v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8;
                    crate::leanh::lean_inc(v_fst_1676_);
                    v___x_1696_ = l_Lean_Syntax_isOfKind(v_fst_1676_, v___x_1695_);
                    if v___x_1696_ == 0 {
                        crate::leanh::lean_dec(v_e_1690_);
                        crate::leanh::lean_del_object(v___x_1684_);
                        crate::leanh::lean_del_object(v___x_1679_);
                        crate::leanh::lean_dec(v_snd_1677_);
                        crate::leanh::lean_dec(v_fst_1676_);
                        v___x_1697_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1692_);
                        if crate::leanh::lean_obj_tag(v___x_1697_) == 0 {
                            v_a_1698_ = crate::leanh::lean_ctor_get(v___x_1697_, 0);
                            crate::leanh::lean_inc(v_a_1698_);
                            v_a_1699_ = crate::leanh::lean_ctor_get(v___x_1697_, 1);
                            crate::leanh::lean_inc(v_a_1699_);
                            crate::leanh::lean_dec_ref_known(v___x_1697_, 2);
                            v_e_1665_ = v_a_1698_;
                            v___y_1666_ = v_a_1699_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1700_ = crate::leanh::lean_ctor_get(v___x_1697_, 0);
                            v_a_1701_ = crate::leanh::lean_ctor_get(v___x_1697_, 1);
                            v_isSharedCheck_1708_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1697_)) as u8;
                            if v_isSharedCheck_1708_ == 0 {
                                v___x_1703_ = v___x_1697_;
                                v_isShared_1704_ = v_isSharedCheck_1708_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1701_);
                                crate::leanh::lean_inc(v_a_1700_);
                                crate::leanh::lean_dec(v___x_1697_);
                                v___x_1703_ = crate::leanh::lean_box(0);
                                v_isShared_1704_ = v_isSharedCheck_1708_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_ref_1709_ = crate::leanh::lean_ctor_get(v___y_1691_, 5);
                        v___x_1710_ = l_Lean_SourceInfo_fromRef(v_ref_1709_, v___x_1694_);
                        v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9;
                        crate::leanh::lean_inc(v___x_1710_);
                        if v_isShared_1685_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1684_, 2);
                            crate::leanh::lean_ctor_set(v___x_1684_, 1, v___x_1711_);
                            crate::leanh::lean_ctor_set(v___x_1684_, 0, v___x_1710_);
                            v___x_1713_ = v___x_1684_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1725_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1710_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1711_);
                            v___x_1713_ = v_reuseFailAlloc_1725_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_1726_ = l_Lean_Syntax_getArg(v_fst_1676_, v___x_1687_);
                    v___x_1727_ = l_Lean_Syntax_getArg(v_fst_1676_, v___x_1688_);
                    crate::leanh::lean_dec(v_fst_1676_);
                    v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16;
                    crate::leanh::lean_inc(v___x_1727_);
                    v___x_1729_ = l_Lean_Syntax_isOfKind(v___x_1727_, v___x_1728_);
                    if v___x_1729_ == 0 {
                        v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18;
                        crate::leanh::lean_inc(v___x_1727_);
                        v___x_1731_ = l_Lean_Syntax_isOfKind(v___x_1727_, v___x_1730_);
                        if v___x_1731_ == 0 {
                            crate::leanh::lean_dec(v___x_1727_);
                            crate::leanh::lean_dec(v___x_1726_);
                            crate::leanh::lean_dec(v_e_1690_);
                            crate::leanh::lean_del_object(v___x_1684_);
                            crate::leanh::lean_del_object(v___x_1679_);
                            crate::leanh::lean_dec(v_snd_1677_);
                            v___x_1732_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1692_);
                            if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                                v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                                crate::leanh::lean_inc(v_a_1733_);
                                v_a_1734_ = crate::leanh::lean_ctor_get(v___x_1732_, 1);
                                crate::leanh::lean_inc(v_a_1734_);
                                crate::leanh::lean_dec_ref_known(v___x_1732_, 2);
                                v_e_1665_ = v_a_1733_;
                                v___y_1666_ = v_a_1734_;
                                state = 1;
                                continue;
                            } else {
                                v_a_1735_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                                v_a_1736_ = crate::leanh::lean_ctor_get(v___x_1732_, 1);
                                v_isSharedCheck_1743_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                                if v_isSharedCheck_1743_ == 0 {
                                    v___x_1738_ = v___x_1732_;
                                    v_isShared_1739_ = v_isSharedCheck_1743_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1736_);
                                    crate::leanh::lean_inc(v_a_1735_);
                                    crate::leanh::lean_dec(v___x_1732_);
                                    v___x_1738_ = crate::leanh::lean_box(0);
                                    v_isShared_1739_ = v_isSharedCheck_1743_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            v_ref_1744_ = crate::leanh::lean_ctor_get(v___y_1691_, 5);
                            v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_1744_, v___y_1691_, v___y_1692_);
                            if crate::leanh::lean_obj_tag(v___x_1745_) == 0 {
                                v_a_1746_ = crate::leanh::lean_ctor_get(v___x_1745_, 0);
                                crate::leanh::lean_inc_n(v_a_1746_, 2);
                                v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1745_, 1);
                                crate::leanh::lean_inc(v_a_1747_);
                                crate::leanh::lean_dec_ref_known(v___x_1745_, 2);
                                v___x_1748_ = l_Lean_Syntax_getArg(v___x_1727_, v___x_1687_);
                                crate::leanh::lean_dec(v___x_1727_);
                                v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20;
                                v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21;
                                if v_isShared_1685_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_1684_, 2);
                                    crate::leanh::lean_ctor_set(v___x_1684_, 1, v___x_1750_);
                                    crate::leanh::lean_ctor_set(v___x_1684_, 0, v_a_1746_);
                                    v___x_1752_ = v___x_1684_;
                                    state = 11;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1786_ =
                                        crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1786_,
                                        0,
                                        v_a_1746_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1786_,
                                        1,
                                        v___x_1750_,
                                    );
                                    v___x_1752_ = v_reuseFailAlloc_1786_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1727_);
                                crate::leanh::lean_dec(v___x_1726_);
                                crate::leanh::lean_dec(v_e_1690_);
                                crate::leanh::lean_del_object(v___x_1684_);
                                crate::leanh::lean_del_object(v___x_1679_);
                                crate::leanh::lean_dec(v_snd_1677_);
                                v_a_1787_ = crate::leanh::lean_ctor_get(v___x_1745_, 0);
                                v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1745_, 1);
                                v_isSharedCheck_1795_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1745_)) as u8;
                                if v_isSharedCheck_1795_ == 0 {
                                    v___x_1790_ = v___x_1745_;
                                    v_isShared_1791_ = v_isSharedCheck_1795_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1788_);
                                    crate::leanh::lean_inc(v_a_1787_);
                                    crate::leanh::lean_dec(v___x_1745_);
                                    v___x_1790_ = crate::leanh::lean_box(0);
                                    v_isShared_1791_ = v_isSharedCheck_1795_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_ref_1796_ = crate::leanh::lean_ctor_get(v___y_1691_, 5);
                        v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_1796_, v___y_1691_, v___y_1692_);
                        if crate::leanh::lean_obj_tag(v___x_1797_) == 0 {
                            v_a_1798_ = crate::leanh::lean_ctor_get(v___x_1797_, 0);
                            crate::leanh::lean_inc_n(v_a_1798_, 2);
                            v_a_1799_ = crate::leanh::lean_ctor_get(v___x_1797_, 1);
                            crate::leanh::lean_inc(v_a_1799_);
                            crate::leanh::lean_dec_ref_known(v___x_1797_, 2);
                            v___x_1800_ = l_Lean_Syntax_getArg(v___x_1727_, v___x_1687_);
                            crate::leanh::lean_dec(v___x_1727_);
                            v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20;
                            v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21;
                            if v_isShared_1685_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1684_, 2);
                                crate::leanh::lean_ctor_set(v___x_1684_, 1, v___x_1802_);
                                crate::leanh::lean_ctor_set(v___x_1684_, 0, v_a_1798_);
                                v___x_1804_ = v___x_1684_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_1834_ =
                                    crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1798_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1802_);
                                v___x_1804_ = v_reuseFailAlloc_1834_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1727_);
                            crate::leanh::lean_dec(v___x_1726_);
                            crate::leanh::lean_dec(v_e_1690_);
                            crate::leanh::lean_del_object(v___x_1684_);
                            crate::leanh::lean_del_object(v___x_1679_);
                            crate::leanh::lean_dec(v_snd_1677_);
                            v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1797_, 0);
                            v_a_1836_ = crate::leanh::lean_ctor_get(v___x_1797_, 1);
                            v_isSharedCheck_1843_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1797_)) as u8;
                            if v_isSharedCheck_1843_ == 0 {
                                v___x_1838_ = v___x_1797_;
                                v_isShared_1839_ = v_isSharedCheck_1843_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1836_);
                                crate::leanh::lean_inc(v_a_1835_);
                                crate::leanh::lean_dec(v___x_1797_);
                                v___x_1838_ = crate::leanh::lean_box(0);
                                v_isShared_1839_ = v_isSharedCheck_1843_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                if v_isShared_1704_ == 0 {
                    v___x_1706_ = v___x_1703_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1701_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1706_;
            }
            7 => {
                v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10;
                crate::leanh::lean_inc(v___x_1710_);
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1679_, 2);
                    crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1714_);
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1710_);
                    v___x_1716_ = v___x_1679_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1714_);
                    v___x_1716_ = v_reuseFailAlloc_1724_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_1718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                crate::leanh::lean_inc_n(v___x_1710_, 3);
                v___x_1719_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1710_);
                crate::leanh::lean_ctor_set(v___x_1719_, 1, v___x_1717_);
                crate::leanh::lean_ctor_set(v___x_1719_, 2, v___x_1718_);
                v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14;
                v___x_1721_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1710_);
                crate::leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                v___x_1722_ = l_Lean_Syntax_node2(v___x_1710_, v___x_1717_, v___x_1721_, v_e_1690_);
                v___x_1723_ = l_Lean_Syntax_node6(
                    v___x_1710_,
                    v___x_1686_,
                    v___x_1713_,
                    v_fst_1676_,
                    v___x_1716_,
                    v_snd_1677_,
                    v___x_1719_,
                    v___x_1722_,
                );
                v_e_1665_ = v___x_1723_;
                v___y_1666_ = v___y_1692_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_1739_ == 0 {
                    v___x_1741_ = v___x_1738_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_a_1736_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1741_;
            }
            11 => {
                v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_1754_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                crate::leanh::lean_inc_n(v_a_1746_, 2);
                v___x_1755_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1755_, 0, v_a_1746_);
                crate::leanh::lean_ctor_set(v___x_1755_, 1, v___x_1753_);
                crate::leanh::lean_ctor_set(v___x_1755_, 2, v___x_1754_);
                v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23;
                v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25;
                v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26;
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1679_, 2);
                    crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1758_);
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v_a_1746_);
                    v___x_1760_ = v___x_1679_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1758_);
                    v___x_1760_ = v_reuseFailAlloc_1785_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_n(v_a_1746_, 16);
                v___x_1761_ = l_Lean_Syntax_node2(v_a_1746_, v___x_1757_, v___x_1760_, v___x_1748_);
                crate::leanh::lean_inc_ref_n(v___x_1755_, 3);
                v___x_1762_ = l_Lean_Syntax_node2(v_a_1746_, v___x_1756_, v___x_1755_, v___x_1761_);
                v___x_1763_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1753_, v___x_1762_);
                v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27;
                v___x_1765_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1765_, 0, v_a_1746_);
                crate::leanh::lean_ctor_set(v___x_1765_, 1, v___x_1764_);
                v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29;
                v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31;
                v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32;
                v___x_1769_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1769_, 0, v_a_1746_);
                crate::leanh::lean_ctor_set(v___x_1769_, 1, v___x_1768_);
                v___x_1770_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1753_, v___x_1726_);
                v___x_1771_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1753_, v___x_1770_);
                v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33;
                v___x_1773_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1773_, 0, v_a_1746_);
                crate::leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
                crate::leanh::lean_inc_ref(v___x_1773_);
                crate::leanh::lean_inc_ref(v___x_1769_);
                v___x_1774_ = l_Lean_Syntax_node4(
                    v_a_1746_,
                    v___x_1767_,
                    v___x_1769_,
                    v___x_1771_,
                    v___x_1773_,
                    v_snd_1677_,
                );
                v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35;
                v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36;
                v___x_1777_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1777_, 0, v_a_1746_);
                crate::leanh::lean_ctor_set(v___x_1777_, 1, v___x_1776_);
                v___x_1778_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1775_, v___x_1777_);
                v___x_1779_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1753_, v___x_1778_);
                v___x_1780_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1753_, v___x_1779_);
                v___x_1781_ = l_Lean_Syntax_node4(
                    v_a_1746_,
                    v___x_1767_,
                    v___x_1769_,
                    v___x_1780_,
                    v___x_1773_,
                    v_e_1690_,
                );
                v___x_1782_ = l_Lean_Syntax_node2(v_a_1746_, v___x_1753_, v___x_1774_, v___x_1781_);
                v___x_1783_ = l_Lean_Syntax_node1(v_a_1746_, v___x_1766_, v___x_1782_);
                v___x_1784_ = l_Lean_Syntax_node7(
                    v_a_1746_,
                    v___x_1749_,
                    v___x_1752_,
                    v___x_1755_,
                    v___x_1755_,
                    v___x_1755_,
                    v___x_1763_,
                    v___x_1765_,
                    v___x_1783_,
                );
                v_e_1665_ = v___x_1784_;
                v___y_1666_ = v_a_1747_;
                state = 1;
                continue;
            }
            13 => {
                if v_isShared_1791_ == 0 {
                    v___x_1793_ = v___x_1790_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1788_);
                    v___x_1793_ = v_reuseFailAlloc_1794_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1793_;
            }
            15 => {
                v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_1806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                crate::leanh::lean_inc_n(v_a_1798_, 4);
                v___x_1807_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1807_, 0, v_a_1798_);
                crate::leanh::lean_ctor_set(v___x_1807_, 1, v___x_1805_);
                crate::leanh::lean_ctor_set(v___x_1807_, 2, v___x_1806_);
                v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23;
                crate::leanh::lean_inc_ref(v___x_1807_);
                v___x_1809_ = l_Lean_Syntax_node2(v_a_1798_, v___x_1808_, v___x_1807_, v___x_1800_);
                v___x_1810_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1805_, v___x_1809_);
                v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27;
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1679_, 2);
                    crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1811_);
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v_a_1798_);
                    v___x_1813_ = v___x_1679_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1811_);
                    v___x_1813_ = v_reuseFailAlloc_1833_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29;
                v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31;
                v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32;
                crate::leanh::lean_inc_n(v_a_1798_, 12);
                v___x_1817_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1817_, 0, v_a_1798_);
                crate::leanh::lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                v___x_1818_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1805_, v___x_1726_);
                v___x_1819_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1805_, v___x_1818_);
                v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33;
                v___x_1821_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1821_, 0, v_a_1798_);
                crate::leanh::lean_ctor_set(v___x_1821_, 1, v___x_1820_);
                crate::leanh::lean_inc_ref(v___x_1821_);
                crate::leanh::lean_inc_ref(v___x_1817_);
                v___x_1822_ = l_Lean_Syntax_node4(
                    v_a_1798_,
                    v___x_1815_,
                    v___x_1817_,
                    v___x_1819_,
                    v___x_1821_,
                    v_snd_1677_,
                );
                v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35;
                v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36;
                v___x_1825_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1825_, 0, v_a_1798_);
                crate::leanh::lean_ctor_set(v___x_1825_, 1, v___x_1824_);
                v___x_1826_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1823_, v___x_1825_);
                v___x_1827_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1805_, v___x_1826_);
                v___x_1828_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1805_, v___x_1827_);
                v___x_1829_ = l_Lean_Syntax_node4(
                    v_a_1798_,
                    v___x_1815_,
                    v___x_1817_,
                    v___x_1828_,
                    v___x_1821_,
                    v_e_1690_,
                );
                v___x_1830_ = l_Lean_Syntax_node2(v_a_1798_, v___x_1805_, v___x_1822_, v___x_1829_);
                v___x_1831_ = l_Lean_Syntax_node1(v_a_1798_, v___x_1814_, v___x_1830_);
                crate::leanh::lean_inc_ref_n(v___x_1807_, 2);
                v___x_1832_ = l_Lean_Syntax_node7(
                    v_a_1798_,
                    v___x_1801_,
                    v___x_1804_,
                    v___x_1807_,
                    v___x_1807_,
                    v___x_1807_,
                    v___x_1810_,
                    v___x_1813_,
                    v___x_1831_,
                );
                v_e_1665_ = v___x_1832_;
                v___y_1666_ = v_a_1799_;
                state = 1;
                continue;
            }
            17 => {
                if v_isShared_1839_ == 0 {
                    v___x_1841_ = v___x_1838_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1836_);
                    v___x_1841_ = v_reuseFailAlloc_1842_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1841_;
            }
            19 => {
                if v_isShared_1861_ == 0 {
                    v___x_1863_ = v___x_1860_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1864_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_a_1858_);
                    v___x_1863_ = v_reuseFailAlloc_1864_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(
    mut v_as_1868_: *mut crate::leanh::LeanObject,
    mut v_sz_1869_: *mut crate::leanh::LeanObject,
    mut v_i_1870_: *mut crate::leanh::LeanObject,
    mut v_b_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1874_: usize = 0;
    let mut v_i_boxed_1875_: usize = 0;
    let mut v_res_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1874_ = crate::leanh::lean_unbox_usize(v_sz_1869_);
    crate::leanh::lean_dec(v_sz_1869_);
    v_i_boxed_1875_ = crate::leanh::lean_unbox_usize(v_i_1870_);
    crate::leanh::lean_dec(v_i_1870_);
    v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v_as_1868_, v_sz_boxed_1874_, v_i_boxed_1875_, v_b_1871_, v___y_1872_, v___y_1873_);
    crate::leanh::lean_dec_ref(v___y_1872_);
    crate::leanh::lean_dec_ref(v_as_1868_);
    return v_res_1876_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(
    mut v_sz_1880_: usize,
    mut v_i_1881_: usize,
    mut v_bs_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tks_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_conds_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ts_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = lean_usize_dec_lt(v_i_1881_, v_sz_1880_);
                if v___x_1883_ == 0 {
                    v___x_1884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v_bs_1882_);
                    return v___x_1884_;
                } else {
                    v_v_1885_ = lean_array_uget(v_bs_1882_, v_i_1881_);
                    v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1;
                    crate::leanh::lean_inc(v_v_1885_);
                    v___x_1887_ = l_Lean_Syntax_isOfKind(v_v_1885_, v___x_1886_);
                    if v___x_1887_ == 0 {
                        crate::leanh::lean_dec(v_v_1885_);
                        crate::leanh::lean_dec_ref(v_bs_1882_);
                        v___x_1888_ = crate::leanh::lean_box(0);
                        return v___x_1888_;
                    } else {
                        v___x_1889_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1890_ = l_Lean_Syntax_getArg(v_v_1885_, v___x_1889_);
                        crate::leanh::lean_inc(v___x_1890_);
                        v___x_1891_ = l_Lean_Syntax_isOfKind(v___x_1890_, v___x_1886_);
                        if v___x_1891_ == 0 {
                            crate::leanh::lean_dec(v___x_1890_);
                            crate::leanh::lean_dec(v_v_1885_);
                            crate::leanh::lean_dec_ref(v_bs_1882_);
                            v___x_1892_ = crate::leanh::lean_box(0);
                            return v___x_1892_;
                        } else {
                            v___x_1893_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1894_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_bs_x27_1895_ = lean_array_uset(v_bs_1882_, v_i_1881_, v___x_1889_);
                            v_tks_1896_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1893_);
                            crate::leanh::lean_dec(v___x_1890_);
                            v_conds_1897_ = l_Lean_Syntax_getArg(v_v_1885_, v___x_1893_);
                            v_ts_1898_ = l_Lean_Syntax_getArg(v_v_1885_, v___x_1894_);
                            crate::leanh::lean_dec(v_v_1885_);
                            v___x_1899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1899_, 0, v_conds_1897_);
                            crate::leanh::lean_ctor_set(v___x_1899_, 1, v_ts_1898_);
                            v___x_1900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1900_, 0, v_tks_1896_);
                            crate::leanh::lean_ctor_set(v___x_1900_, 1, v___x_1899_);
                            v___x_1901_ = 1usize;
                            v___x_1902_ = lean_usize_add(v_i_1881_, v___x_1901_);
                            v___x_1903_ = lean_array_uset(v_bs_x27_1895_, v_i_1881_, v___x_1900_);
                            v_i_1881_ = v___x_1902_;
                            v_bs_1882_ = v___x_1903_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(
    mut v_sz_1905_: *mut crate::leanh::LeanObject,
    mut v_i_1906_: *mut crate::leanh::LeanObject,
    mut v_bs_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1908_: usize = 0;
    let mut v_i_boxed_1909_: usize = 0;
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1908_ = crate::leanh::lean_unbox_usize(v_sz_1905_);
    crate::leanh::lean_dec(v_sz_1905_);
    v_i_boxed_1909_ = crate::leanh::lean_unbox_usize(v_i_1906_);
    crate::leanh::lean_dec(v_i_1906_);
    v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_boxed_1908_, v_i_boxed_1909_, v_bs_1907_);
    return v_res_1910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(
    mut v_sz_1911_: usize,
    mut v_i_1912_: usize,
    mut v_bs_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: u8 = 0;
    let mut v_v_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: usize = 0;
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1914_ = lean_usize_dec_lt(v_i_1912_, v_sz_1911_);
                if v___x_1914_ == 0 {
                    return v_bs_1913_;
                } else {
                    v_v_1915_ = lean_array_uget_borrowed(v_bs_1913_, v_i_1912_);
                    v_snd_1916_ = crate::leanh::lean_ctor_get(v_v_1915_, 1);
                    v_fst_1917_ = crate::leanh::lean_ctor_get(v_snd_1916_, 0);
                    crate::leanh::lean_inc(v_fst_1917_);
                    v___x_1918_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1919_ = lean_array_uset(v_bs_1913_, v_i_1912_, v___x_1918_);
                    v___x_1920_ = 1usize;
                    v___x_1921_ = lean_usize_add(v_i_1912_, v___x_1920_);
                    v___x_1922_ = lean_array_uset(v_bs_x27_1919_, v_i_1912_, v_fst_1917_);
                    v_i_1912_ = v___x_1921_;
                    v_bs_1913_ = v___x_1922_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(
    mut v_sz_1924_: *mut crate::leanh::LeanObject,
    mut v_i_1925_: *mut crate::leanh::LeanObject,
    mut v_bs_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1927_: usize = 0;
    let mut v_i_boxed_1928_: usize = 0;
    let mut v_res_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1927_ = crate::leanh::lean_unbox_usize(v_sz_1924_);
    crate::leanh::lean_dec(v_sz_1924_);
    v_i_boxed_1928_ = crate::leanh::lean_unbox_usize(v_i_1925_);
    crate::leanh::lean_dec(v_i_1925_);
    v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_boxed_1927_, v_i_boxed_1928_, v_bs_1926_);
    return v_res_1929_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(
    mut v_sz_1930_: usize,
    mut v_i_1931_: usize,
    mut v_bs_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1933_: u8 = 0;
    let mut v_v_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: usize = 0;
    let mut v___x_1940_: usize = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1933_ = lean_usize_dec_lt(v_i_1931_, v_sz_1930_);
                if v___x_1933_ == 0 {
                    return v_bs_1932_;
                } else {
                    v_v_1934_ = lean_array_uget_borrowed(v_bs_1932_, v_i_1931_);
                    v_snd_1935_ = crate::leanh::lean_ctor_get(v_v_1934_, 1);
                    v_snd_1936_ = crate::leanh::lean_ctor_get(v_snd_1935_, 1);
                    crate::leanh::lean_inc(v_snd_1936_);
                    v___x_1937_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1938_ = lean_array_uset(v_bs_1932_, v_i_1931_, v___x_1937_);
                    v___x_1939_ = 1usize;
                    v___x_1940_ = lean_usize_add(v_i_1931_, v___x_1939_);
                    v___x_1941_ = lean_array_uset(v_bs_x27_1938_, v_i_1931_, v_snd_1936_);
                    v_i_1931_ = v___x_1940_;
                    v_bs_1932_ = v___x_1941_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1___boxed(
    mut v_sz_1943_: *mut crate::leanh::LeanObject,
    mut v_i_1944_: *mut crate::leanh::LeanObject,
    mut v_bs_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1946_: usize = 0;
    let mut v_i_boxed_1947_: usize = 0;
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1946_ = crate::leanh::lean_unbox_usize(v_sz_1943_);
    crate::leanh::lean_dec(v_sz_1943_);
    v_i_boxed_1947_ = crate::leanh::lean_unbox_usize(v_i_1944_);
    crate::leanh::lean_dec(v_i_1944_);
    v_res_1948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_boxed_1946_, v_i_boxed_1947_, v_bs_1945_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_Elab_Do_expandDoIf(
    mut v_stx_1958_: *mut crate::leanh::LeanObject,
    mut v_a_1959_: *mut crate::leanh::LeanObject,
    mut v_a_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eIsSeq_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cond_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1973_: usize = 0;
    let mut v___x_1974_: usize = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1980_: usize = 0;
    let mut v_ts_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_conds_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1994_: usize = 0;
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2000_: u8 = 0;
    let mut v_fst_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut v_a_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2053_: usize = 0;
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v_fst_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v_a_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_conds_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ts_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2100_: usize = 0;
    let mut v___x_2101_: usize = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2105_: usize = 0;
    let mut v_ts_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_conds_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: u8 = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2118_: usize = 0;
    let mut v___x_2119_: usize = 0;
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2123_: usize = 0;
    let mut v_ts_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_conds_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4;
                crate::leanh::lean_inc(v_stx_1958_);
                v_eIsSeq_1962_ = l_Lean_Syntax_isOfKind(v_stx_1958_, v___x_1961_);
                if v_eIsSeq_1962_ == 0 {
                    crate::leanh::lean_dec(v_stx_1958_);
                    v___x_1963_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                    return v___x_1963_;
                } else {
                    v___x_1964_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_1965_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_1964_);
                    v___x_1966_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_cond_1967_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_1966_);
                    v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8;
                    crate::leanh::lean_inc(v_cond_1967_);
                    v___x_1969_ = l_Lean_Syntax_isOfKind(v_cond_1967_, v___x_1968_);
                    if v___x_1969_ == 0 {
                        v___x_1970_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_1971_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_1970_);
                        v___x_1972_ = l_Lean_Syntax_getArgs(v___x_1971_);
                        crate::leanh::lean_dec(v___x_1971_);
                        v_sz_1973_ = lean_array_size(v___x_1972_);
                        v___x_1974_ = 0usize;
                        v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_1973_, v___x_1974_, v___x_1972_);
                        if crate::leanh::lean_obj_tag(v___x_1975_) == 0 {
                            crate::leanh::lean_dec(v_cond_1967_);
                            crate::leanh::lean_dec(v_tk_1965_);
                            crate::leanh::lean_dec(v_stx_1958_);
                            v___x_1976_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                            return v___x_1976_;
                        } else {
                            v_val_1977_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                            crate::leanh::lean_inc_n(v_val_1977_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_1975_, 1);
                            v___x_1978_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_t_1979_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_1978_);
                            v_sz_1980_ = lean_array_size(v_val_1977_);
                            v_ts_1981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_1980_, v___x_1974_, v_val_1977_);
                            v_conds_1982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_1980_, v___x_1974_, v_val_1977_);
                            v___x_2015_ = crate::leanh::lean_unsigned_to_nat(5);
                            v___x_2016_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_2015_);
                            crate::leanh::lean_dec(v_stx_1958_);
                            v___x_2017_ = l_Lean_Syntax_isNone(v___x_2016_);
                            if v___x_2017_ == 0 {
                                crate::leanh::lean_dec(v_tk_1965_);
                                v___x_2018_ = crate::leanh::lean_unsigned_to_nat(2);
                                crate::leanh::lean_inc(v___x_2016_);
                                v___x_2019_ = l_Lean_Syntax_matchesNull(v___x_2016_, v___x_2018_);
                                if v___x_2019_ == 0 {
                                    crate::leanh::lean_dec(v___x_2016_);
                                    crate::leanh::lean_dec_ref(v_conds_1982_);
                                    crate::leanh::lean_dec_ref(v_ts_1981_);
                                    crate::leanh::lean_dec(v_t_1979_);
                                    crate::leanh::lean_dec(v_cond_1967_);
                                    v___x_2020_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                                    return v___x_2020_;
                                } else {
                                    v_e_x3f_2021_ = l_Lean_Syntax_getArg(v___x_2016_, v___x_1966_);
                                    crate::leanh::lean_dec(v___x_2016_);
                                    v___y_1984_ = v_a_1959_;
                                    v_a_1985_ = v_e_x3f_2021_;
                                    v_a_1986_ = v_a_1960_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2016_);
                                v_ref_2022_ = crate::leanh::lean_ctor_get(v_a_1959_, 5);
                                v___x_2023_ = l_Lean_SourceInfo_fromRef(v_ref_2022_, v___x_1969_);
                                v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38;
                                v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                                v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40;
                                v___x_2027_ = l_Lean_Elab_Do_expandDoIf___closed__2;
                                v___x_2028_ = l_Lean_SourceInfo_fromRef(v_tk_1965_, v_eIsSeq_1962_);
                                crate::leanh::lean_dec(v_tk_1965_);
                                v___x_2029_ = l_Lean_Elab_Do_expandDoIf___closed__3;
                                v___x_2030_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2030_, 0, v___x_2028_);
                                crate::leanh::lean_ctor_set(v___x_2030_, 1, v___x_2029_);
                                crate::leanh::lean_inc_n(v___x_2023_, 4);
                                v___x_2031_ =
                                    l_Lean_Syntax_node1(v___x_2023_, v___x_2027_, v___x_2030_);
                                v___x_2032_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                                v___x_2033_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2023_);
                                crate::leanh::lean_ctor_set(v___x_2033_, 1, v___x_2025_);
                                crate::leanh::lean_ctor_set(v___x_2033_, 2, v___x_2032_);
                                v___x_2034_ = l_Lean_Syntax_node2(
                                    v___x_2023_,
                                    v___x_2026_,
                                    v___x_2031_,
                                    v___x_2033_,
                                );
                                v___x_2035_ =
                                    l_Lean_Syntax_node1(v___x_2023_, v___x_2025_, v___x_2034_);
                                v___x_2036_ =
                                    l_Lean_Syntax_node1(v___x_2023_, v___x_2024_, v___x_2035_);
                                v___y_1984_ = v_a_1959_;
                                v_a_1985_ = v___x_2036_;
                                v_a_1986_ = v_a_1960_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_2037_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2038_ = crate::leanh::lean_unsigned_to_nat(3);
                        v_t_2039_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_2038_);
                        v___x_2096_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_2097_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_2096_);
                        crate::leanh::lean_inc(v___x_2097_);
                        v___x_2098_ = l_Lean_Syntax_matchesNull(v___x_2097_, v___x_1964_);
                        if v___x_2098_ == 0 {
                            v___x_2099_ = l_Lean_Syntax_getArgs(v___x_2097_);
                            crate::leanh::lean_dec(v___x_2097_);
                            v_sz_2100_ = lean_array_size(v___x_2099_);
                            v___x_2101_ = 0usize;
                            v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_2100_, v___x_2101_, v___x_2099_);
                            if crate::leanh::lean_obj_tag(v___x_2102_) == 0 {
                                crate::leanh::lean_dec(v_t_2039_);
                                crate::leanh::lean_dec(v_cond_1967_);
                                crate::leanh::lean_dec(v_tk_1965_);
                                crate::leanh::lean_dec(v_stx_1958_);
                                v___x_2103_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                                return v___x_2103_;
                            } else {
                                v_val_2104_ = crate::leanh::lean_ctor_get(v___x_2102_, 0);
                                crate::leanh::lean_inc_n(v_val_2104_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_2102_, 1);
                                v_sz_2105_ = lean_array_size(v_val_2104_);
                                v_ts_2106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_2105_, v___x_2101_, v_val_2104_);
                                v_conds_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_2105_, v___x_2101_, v_val_2104_);
                                v___x_2108_ = crate::leanh::lean_unsigned_to_nat(5);
                                v___x_2109_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_2108_);
                                crate::leanh::lean_dec(v_stx_1958_);
                                v___x_2110_ = l_Lean_Syntax_isNone(v___x_2109_);
                                if v___x_2110_ == 0 {
                                    crate::leanh::lean_dec(v_tk_1965_);
                                    crate::leanh::lean_inc(v___x_2109_);
                                    v___x_2111_ =
                                        l_Lean_Syntax_matchesNull(v___x_2109_, v___x_2037_);
                                    if v___x_2111_ == 0 {
                                        crate::leanh::lean_dec(v___x_2109_);
                                        crate::leanh::lean_dec_ref(v_conds_2107_);
                                        crate::leanh::lean_dec_ref(v_ts_2106_);
                                        crate::leanh::lean_dec(v_t_2039_);
                                        crate::leanh::lean_dec(v_cond_1967_);
                                        v___x_2112_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                                        return v___x_2112_;
                                    } else {
                                        v_e_x3f_2113_ =
                                            l_Lean_Syntax_getArg(v___x_2109_, v___x_1966_);
                                        crate::leanh::lean_dec(v___x_2109_);
                                        v___y_2041_ = v_conds_2107_;
                                        v___y_2042_ = v_ts_2106_;
                                        v___y_2043_ = v_a_1959_;
                                        v_a_2044_ = v_e_x3f_2113_;
                                        v_a_2045_ = v_a_1960_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2109_);
                                    v_conds_2076_ = v_conds_2107_;
                                    v_ts_2077_ = v_ts_2106_;
                                    v___y_2078_ = v_a_1959_;
                                    v___y_2079_ = v_a_1960_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2114_ = crate::leanh::lean_unsigned_to_nat(5);
                            v___x_2115_ = l_Lean_Syntax_getArg(v_stx_1958_, v___x_2114_);
                            crate::leanh::lean_dec(v_stx_1958_);
                            crate::leanh::lean_inc(v___x_2115_);
                            v___x_2116_ = l_Lean_Syntax_matchesNull(v___x_2115_, v___x_2037_);
                            if v___x_2116_ == 0 {
                                v___x_2117_ = l_Lean_Syntax_getArgs(v___x_2097_);
                                crate::leanh::lean_dec(v___x_2097_);
                                v_sz_2118_ = lean_array_size(v___x_2117_);
                                v___x_2119_ = 0usize;
                                v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_2118_, v___x_2119_, v___x_2117_);
                                if crate::leanh::lean_obj_tag(v___x_2120_) == 0 {
                                    crate::leanh::lean_dec(v___x_2115_);
                                    crate::leanh::lean_dec(v_t_2039_);
                                    crate::leanh::lean_dec(v_cond_1967_);
                                    crate::leanh::lean_dec(v_tk_1965_);
                                    v___x_2121_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                                    return v___x_2121_;
                                } else {
                                    v_val_2122_ = crate::leanh::lean_ctor_get(v___x_2120_, 0);
                                    crate::leanh::lean_inc_n(v_val_2122_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_2120_, 1);
                                    v_sz_2123_ = lean_array_size(v_val_2122_);
                                    v_ts_2124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_2123_, v___x_2119_, v_val_2122_);
                                    v_conds_2125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_2123_, v___x_2119_, v_val_2122_);
                                    v___x_2126_ = l_Lean_Syntax_isNone(v___x_2115_);
                                    if v___x_2126_ == 0 {
                                        crate::leanh::lean_dec(v_tk_1965_);
                                        if v___x_2116_ == 0 {
                                            crate::leanh::lean_dec_ref(v_conds_2125_);
                                            crate::leanh::lean_dec_ref(v_ts_2124_);
                                            crate::leanh::lean_dec(v___x_2115_);
                                            crate::leanh::lean_dec(v_t_2039_);
                                            crate::leanh::lean_dec(v_cond_1967_);
                                            v___x_2127_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                                            return v___x_2127_;
                                        } else {
                                            v_e_x3f_2128_ =
                                                l_Lean_Syntax_getArg(v___x_2115_, v___x_1966_);
                                            crate::leanh::lean_dec(v___x_2115_);
                                            v___y_2041_ = v_conds_2125_;
                                            v___y_2042_ = v_ts_2124_;
                                            v___y_2043_ = v_a_1959_;
                                            v_a_2044_ = v_e_x3f_2128_;
                                            v_a_2045_ = v_a_1960_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2115_);
                                        v_conds_2076_ = v_conds_2125_;
                                        v_ts_2077_ = v_ts_2124_;
                                        v___y_2078_ = v_a_1959_;
                                        v___y_2079_ = v_a_1960_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2115_);
                                crate::leanh::lean_dec(v___x_2097_);
                                crate::leanh::lean_dec(v_t_2039_);
                                crate::leanh::lean_dec(v_cond_1967_);
                                crate::leanh::lean_dec(v_tk_1965_);
                                v___x_2129_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1960_);
                                return v___x_2129_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1987_ = l_Array_reverse___redArg(v_conds_1982_);
                v___x_1988_ = lean_array_push(v___x_1987_, v_cond_1967_);
                v___x_1989_ = l_Array_reverse___redArg(v_ts_1981_);
                v___x_1990_ = lean_array_push(v___x_1989_, v_t_1979_);
                v___x_1991_ = l_Array_zip___redArg(v___x_1988_, v___x_1990_);
                crate::leanh::lean_dec_ref(v___x_1990_);
                crate::leanh::lean_dec_ref(v___x_1988_);
                v___x_1992_ = crate::leanh::lean_box((v_eIsSeq_1962_) as usize);
                v___x_1993_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1993_, 0, v_a_1985_);
                crate::leanh::lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                v_sz_1994_ = lean_array_size(v___x_1991_);
                v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_1969_, v___x_1991_, v_sz_1994_, v___x_1974_, v___x_1993_, v___y_1984_, v_a_1986_);
                crate::leanh::lean_dec_ref(v___x_1991_);
                if crate::leanh::lean_obj_tag(v___x_1995_) == 0 {
                    v_a_1996_ = crate::leanh::lean_ctor_get(v___x_1995_, 0);
                    v_a_1997_ = crate::leanh::lean_ctor_get(v___x_1995_, 1);
                    v_isSharedCheck_2005_ = (!crate::leanh::lean_is_exclusive(v___x_1995_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1999_ = v___x_1995_;
                        v_isShared_2000_ = v_isSharedCheck_2005_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1997_);
                        crate::leanh::lean_inc(v_a_1996_);
                        crate::leanh::lean_dec(v___x_1995_);
                        v___x_1999_ = crate::leanh::lean_box(0);
                        v_isShared_2000_ = v_isSharedCheck_2005_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2006_ = crate::leanh::lean_ctor_get(v___x_1995_, 0);
                    v_a_2007_ = crate::leanh::lean_ctor_get(v___x_1995_, 1);
                    v_isSharedCheck_2014_ = (!crate::leanh::lean_is_exclusive(v___x_1995_)) as u8;
                    if v_isSharedCheck_2014_ == 0 {
                        v___x_2009_ = v___x_1995_;
                        v_isShared_2010_ = v_isSharedCheck_2014_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2007_);
                        crate::leanh::lean_inc(v_a_2006_);
                        crate::leanh::lean_dec(v___x_1995_);
                        v___x_2009_ = crate::leanh::lean_box(0);
                        v_isShared_2010_ = v_isSharedCheck_2014_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2001_ = crate::leanh::lean_ctor_get(v_a_1996_, 0);
                crate::leanh::lean_inc(v_fst_2001_);
                crate::leanh::lean_dec(v_a_1996_);
                if v_isShared_2000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1999_, 0, v_fst_2001_);
                    v___x_2003_ = v___x_1999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_fst_2001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_a_1997_);
                    v___x_2003_ = v_reuseFailAlloc_2004_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2003_;
            }
            4 => {
                if v_isShared_2010_ == 0 {
                    v___x_2012_ = v___x_2009_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_a_2007_);
                    v___x_2012_ = v_reuseFailAlloc_2013_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2012_;
            }
            6 => {
                v___x_2046_ = l_Array_reverse___redArg(v___y_2041_);
                v___x_2047_ = lean_array_push(v___x_2046_, v_cond_1967_);
                v___x_2048_ = l_Array_reverse___redArg(v___y_2042_);
                v___x_2049_ = lean_array_push(v___x_2048_, v_t_2039_);
                v___x_2050_ = l_Array_zip___redArg(v___x_2047_, v___x_2049_);
                crate::leanh::lean_dec_ref(v___x_2049_);
                crate::leanh::lean_dec_ref(v___x_2047_);
                v___x_2051_ = crate::leanh::lean_box((v_eIsSeq_1962_) as usize);
                v___x_2052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2052_, 0, v_a_2044_);
                crate::leanh::lean_ctor_set(v___x_2052_, 1, v___x_2051_);
                v_sz_2053_ = lean_array_size(v___x_2050_);
                v___x_2054_ = 0usize;
                v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v___x_2050_, v_sz_2053_, v___x_2054_, v___x_2052_, v___y_2043_, v_a_2045_);
                crate::leanh::lean_dec_ref(v___x_2050_);
                if crate::leanh::lean_obj_tag(v___x_2055_) == 0 {
                    v_a_2056_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                    v_a_2057_ = crate::leanh::lean_ctor_get(v___x_2055_, 1);
                    v_isSharedCheck_2065_ = (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2059_ = v___x_2055_;
                        v_isShared_2060_ = v_isSharedCheck_2065_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2057_);
                        crate::leanh::lean_inc(v_a_2056_);
                        crate::leanh::lean_dec(v___x_2055_);
                        v___x_2059_ = crate::leanh::lean_box(0);
                        v_isShared_2060_ = v_isSharedCheck_2065_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2066_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                    v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2055_, 1);
                    v_isSharedCheck_2074_ = (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2055_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2067_);
                        crate::leanh::lean_inc(v_a_2066_);
                        crate::leanh::lean_dec(v___x_2055_);
                        v___x_2069_ = crate::leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v_fst_2061_ = crate::leanh::lean_ctor_get(v_a_2056_, 0);
                crate::leanh::lean_inc(v_fst_2061_);
                crate::leanh::lean_dec(v_a_2056_);
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v_fst_2061_);
                    v___x_2063_ = v___x_2059_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_fst_2061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_a_2057_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2063_;
            }
            9 => {
                if v_isShared_2070_ == 0 {
                    v___x_2072_ = v___x_2069_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_a_2067_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2072_;
            }
            11 => {
                v_ref_2080_ = crate::leanh::lean_ctor_get(v___y_2078_, 5);
                v___x_2081_ = 0;
                v___x_2082_ = l_Lean_SourceInfo_fromRef(v_ref_2080_, v___x_2081_);
                v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38;
                v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12;
                v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40;
                v___x_2086_ = l_Lean_Elab_Do_expandDoIf___closed__2;
                v___x_2087_ = l_Lean_SourceInfo_fromRef(v_tk_1965_, v_eIsSeq_1962_);
                crate::leanh::lean_dec(v_tk_1965_);
                v___x_2088_ = l_Lean_Elab_Do_expandDoIf___closed__3;
                v___x_2089_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2087_);
                crate::leanh::lean_ctor_set(v___x_2089_, 1, v___x_2088_);
                crate::leanh::lean_inc_n(v___x_2082_, 4);
                v___x_2090_ = l_Lean_Syntax_node1(v___x_2082_, v___x_2086_, v___x_2089_);
                v___x_2091_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
                v___x_2092_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2092_, 0, v___x_2082_);
                crate::leanh::lean_ctor_set(v___x_2092_, 1, v___x_2084_);
                crate::leanh::lean_ctor_set(v___x_2092_, 2, v___x_2091_);
                v___x_2093_ =
                    l_Lean_Syntax_node2(v___x_2082_, v___x_2085_, v___x_2090_, v___x_2092_);
                v___x_2094_ = l_Lean_Syntax_node1(v___x_2082_, v___x_2084_, v___x_2093_);
                v___x_2095_ = l_Lean_Syntax_node1(v___x_2082_, v___x_2083_, v___x_2094_);
                v___y_2041_ = v_conds_2076_;
                v___y_2042_ = v_ts_2077_;
                v___y_2043_ = v___y_2078_;
                v_a_2044_ = v___x_2095_;
                v_a_2045_ = v___y_2079_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_expandDoIf___boxed(
    mut v_stx_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2133_ = l_Lean_Elab_Do_expandDoIf(v_stx_2130_, v_a_2131_, v_a_2132_);
    crate::leanh::lean_dec_ref(v_a_2131_);
    return v_res_2133_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Elab_macroAttribute;
    v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4;
    v___x_2145_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3;
    v___x_2146_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_expandDoIf___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_2147_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2143_,
        v___x_2144_,
        v___x_2145_,
        v___x_2146_,
    );
    return v___x_2147_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(
    mut v_a_2148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2149_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
    return v_res_2149_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2152_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3;
    v___x_2153_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0;
    v___x_2154_ = l_Lean_addBuiltinDocString(v___x_2152_, v___x_2153_);
    return v___x_2154_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(
    mut v_a_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
    return v_res_2156_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(
    mut v_cond_2160_: *mut crate::leanh::LeanObject,
    mut v_then___2161_: *mut crate::leanh::LeanObject,
    mut v___x_2162_: u8,
    mut v_else___2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doBlockResultType_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v_ref_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doBlockResultType_2172_ = crate::leanh::lean_ctor_get(v___y_2164_, 3);
                crate::leanh::lean_inc_ref(v_doBlockResultType_2172_);
                v___x_2173_ = l_Lean_Elab_Do_mkMonadApp(
                    v_doBlockResultType_2172_,
                    v___y_2164_,
                    v___y_2165_,
                    v___y_2166_,
                    v___y_2167_,
                    v___y_2168_,
                    v___y_2169_,
                    v___y_2170_,
                );
                if crate::leanh::lean_obj_tag(v___x_2173_) == 0 {
                    v_a_2174_ = crate::leanh::lean_ctor_get(v___x_2173_, 0);
                    v_isSharedCheck_2194_ = (!crate::leanh::lean_is_exclusive(v___x_2173_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2176_ = v___x_2173_;
                        v_isShared_2177_ = v_isSharedCheck_2194_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2174_);
                        crate::leanh::lean_dec(v___x_2173_);
                        v___x_2176_ = crate::leanh::lean_box(0);
                        v_isShared_2177_ = v_isSharedCheck_2194_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_else___2163_);
                    crate::leanh::lean_dec(v_then___2161_);
                    crate::leanh::lean_dec(v_cond_2160_);
                    return v___x_2173_;
                }
            }
            1 => {
                v_ref_2178_ = crate::leanh::lean_ctor_get(v___y_2169_, 5);
                v___x_2179_ = 0;
                v___x_2180_ = l_Lean_SourceInfo_fromRef(v_ref_2178_, v___x_2179_);
                v___x_2181_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1;
                v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9;
                crate::leanh::lean_inc_n(v___x_2180_, 3);
                v___x_2183_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2180_);
                crate::leanh::lean_ctor_set(v___x_2183_, 1, v___x_2182_);
                v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10;
                v___x_2185_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2185_, 0, v___x_2180_);
                crate::leanh::lean_ctor_set(v___x_2185_, 1, v___x_2184_);
                v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14;
                v___x_2187_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2180_);
                crate::leanh::lean_ctor_set(v___x_2187_, 1, v___x_2186_);
                v___x_2188_ = l_Lean_Syntax_node6(
                    v___x_2180_,
                    v___x_2181_,
                    v___x_2183_,
                    v_cond_2160_,
                    v___x_2185_,
                    v_then___2161_,
                    v___x_2187_,
                    v_else___2163_,
                );
                if v_isShared_2177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2176_, 1);
                    v___x_2190_ = v___x_2176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2174_);
                    v___x_2190_ = v_reuseFailAlloc_2193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2191_ = crate::leanh::lean_box(0);
                v___x_2192_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_2188_,
                    v___x_2190_,
                    v___x_2162_,
                    v___x_2162_,
                    v___x_2191_,
                    v___y_2165_,
                    v___y_2166_,
                    v___y_2167_,
                    v___y_2168_,
                    v___y_2169_,
                    v___y_2170_,
                );
                return v___x_2192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(
    mut v_cond_2195_: *mut crate::leanh::LeanObject,
    mut v_then___2196_: *mut crate::leanh::LeanObject,
    mut v___x_2197_: *mut crate::leanh::LeanObject,
    mut v_else___2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3198__boxed_2207_: u8 = 0;
    let mut v_res_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3198__boxed_2207_ = (crate::leanh::lean_unbox(v___x_2197_) as u8);
    v_res_2208_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(
        v_cond_2195_,
        v_then___2196_,
        v___x_3198__boxed_2207_,
        v_else___2198_,
        v___y_2199_,
        v___y_2200_,
        v___y_2201_,
        v___y_2202_,
        v___y_2203_,
        v___y_2204_,
        v___y_2205_,
    );
    crate::leanh::lean_dec(v___y_2205_);
    crate::leanh::lean_dec_ref(v___y_2204_);
    crate::leanh::lean_dec(v___y_2203_);
    crate::leanh::lean_dec_ref(v___y_2202_);
    crate::leanh::lean_dec(v___y_2201_);
    crate::leanh::lean_dec_ref(v___y_2200_);
    crate::leanh::lean_dec_ref(v___y_2199_);
    return v_res_2208_;
}
pub unsafe fn _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ =
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1;
    v___x_2213_ = l_Lean_MessageData_ofFormat(v___x_2212_);
    return v___x_2213_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(
    mut v_cond_2214_: *mut crate::leanh::LeanObject,
    mut v___x_2215_: u8,
    mut v_elseSeq_2216_: *mut crate::leanh::LeanObject,
    mut v_dec_2217_: *mut crate::leanh::LeanObject,
    mut v_then___2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2227_ = crate::leanh::lean_box((v___x_2215_) as usize);
    v___f_2228_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2228_, 0, v_cond_2214_);
    crate::leanh::lean_closure_set(v___f_2228_, 1, v_then___2218_);
    crate::leanh::lean_closure_set(v___f_2228_, 2, v___x_2227_);
    v___x_2229_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once), _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
    v___x_2230_ = crate::leanh::lean_box((v___x_2215_) as usize);
    v___x_2231_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2231_, 0, v_elseSeq_2216_);
    crate::leanh::lean_closure_set(v___x_2231_, 1, v_dec_2217_);
    crate::leanh::lean_closure_set(v___x_2231_, 2, v___x_2230_);
    v___x_2232_ = crate::leanh::lean_box(0);
    v___x_2233_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
        v___x_2229_,
        v___x_2231_,
        v___f_2228_,
        v___x_2232_,
        v___y_2219_,
        v___y_2220_,
        v___y_2221_,
        v___y_2222_,
        v___y_2223_,
        v___y_2224_,
        v___y_2225_,
    );
    return v___x_2233_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(
    mut v_cond_2234_: *mut crate::leanh::LeanObject,
    mut v___x_2235_: *mut crate::leanh::LeanObject,
    mut v_elseSeq_2236_: *mut crate::leanh::LeanObject,
    mut v_dec_2237_: *mut crate::leanh::LeanObject,
    mut v_then___2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3281__boxed_2247_: u8 = 0;
    let mut v_res_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3281__boxed_2247_ = (crate::leanh::lean_unbox(v___x_2235_) as u8);
    v_res_2248_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(
        v_cond_2234_,
        v___x_3281__boxed_2247_,
        v_elseSeq_2236_,
        v_dec_2237_,
        v_then___2238_,
        v___y_2239_,
        v___y_2240_,
        v___y_2241_,
        v___y_2242_,
        v___y_2243_,
        v___y_2244_,
        v___y_2245_,
    );
    crate::leanh::lean_dec(v___y_2245_);
    crate::leanh::lean_dec_ref(v___y_2244_);
    crate::leanh::lean_dec(v___y_2243_);
    crate::leanh::lean_dec_ref(v___y_2242_);
    crate::leanh::lean_dec(v___y_2241_);
    crate::leanh::lean_dec_ref(v___y_2240_);
    crate::leanh::lean_dec_ref(v___y_2239_);
    return v_res_2248_;
}
pub unsafe fn _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1;
    v___x_2253_ = l_Lean_MessageData_ofFormat(v___x_2252_);
    return v___x_2253_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(
    mut v_cond_2254_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2255_: *mut crate::leanh::LeanObject,
    mut v_elseSeq_2256_: *mut crate::leanh::LeanObject,
    mut v_dec_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
    mut v_a_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once
        ),
        _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2,
    );
    v___x_2267_ = 1;
    v___x_2268_ = crate::leanh::lean_box((v___x_2267_) as usize);
    crate::leanh::lean_inc_ref(v_dec_2257_);
    v___f_2269_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed
            as *mut core::ffi::c_void,
        13,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2269_, 0, v_cond_2254_);
    crate::leanh::lean_closure_set(v___f_2269_, 1, v___x_2268_);
    crate::leanh::lean_closure_set(v___f_2269_, 2, v_elseSeq_2256_);
    crate::leanh::lean_closure_set(v___f_2269_, 3, v_dec_2257_);
    v___x_2270_ = crate::leanh::lean_box((v___x_2267_) as usize);
    v___x_2271_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2271_, 0, v_thenSeq_2255_);
    crate::leanh::lean_closure_set(v___x_2271_, 1, v_dec_2257_);
    crate::leanh::lean_closure_set(v___x_2271_, 2, v___x_2270_);
    v___x_2272_ = crate::leanh::lean_box(0);
    v___x_2273_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
        v___x_2266_,
        v___x_2271_,
        v___f_2269_,
        v___x_2272_,
        v_a_2258_,
        v_a_2259_,
        v_a_2260_,
        v_a_2261_,
        v_a_2262_,
        v_a_2263_,
        v_a_2264_,
    );
    return v___x_2273_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(
    mut v_cond_2274_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2275_: *mut crate::leanh::LeanObject,
    mut v_elseSeq_2276_: *mut crate::leanh::LeanObject,
    mut v_dec_2277_: *mut crate::leanh::LeanObject,
    mut v_a_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(
        v_cond_2274_,
        v_thenSeq_2275_,
        v_elseSeq_2276_,
        v_dec_2277_,
        v_a_2278_,
        v_a_2279_,
        v_a_2280_,
        v_a_2281_,
        v_a_2282_,
        v_a_2283_,
        v_a_2284_,
    );
    crate::leanh::lean_dec(v_a_2284_);
    crate::leanh::lean_dec_ref(v_a_2283_);
    crate::leanh::lean_dec(v_a_2282_);
    crate::leanh::lean_dec_ref(v_a_2281_);
    crate::leanh::lean_dec(v_a_2280_);
    crate::leanh::lean_dec_ref(v_a_2279_);
    crate::leanh::lean_dec_ref(v_a_2278_);
    return v_res_2286_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2287_ = crate::leanh::lean_box(0);
    v___x_2288_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2289_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2288_);
    crate::leanh::lean_ctor_set(v___x_2289_, 1, v___x_2287_);
    return v___x_2289_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2291_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0);
    v___x_2292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2292_, 0, v___x_2291_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(
    mut v___y_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
    return v_res_2294_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(
    mut v_00_u03b1_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
    return v___x_2304_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(
    mut v_00_u03b1_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(v_00_u03b1_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    crate::leanh::lean_dec(v___y_2312_);
    crate::leanh::lean_dec_ref(v___y_2311_);
    crate::leanh::lean_dec(v___y_2310_);
    crate::leanh::lean_dec_ref(v___y_2309_);
    crate::leanh::lean_dec(v___y_2308_);
    crate::leanh::lean_dec_ref(v___y_2307_);
    crate::leanh::lean_dec_ref(v___y_2306_);
    return v_res_2314_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(
    mut v_elseSeq_2315_: *mut crate::leanh::LeanObject,
    mut v_dec_2316_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2317_: *mut crate::leanh::LeanObject,
    mut v_then___2318_: u8,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: u8 = 0;
    v___x_2327_ = 1;
    if v_then___2318_ == 0 {
        let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_thenSeq_2317_);
        v___x_2328_ = l_Lean_Elab_Do_elabDoSeq(
            v_elseSeq_2315_,
            v_dec_2316_,
            v___x_2327_,
            v___y_2319_,
            v___y_2320_,
            v___y_2321_,
            v___y_2322_,
            v___y_2323_,
            v___y_2324_,
            v___y_2325_,
        );
        return v___x_2328_;
    } else {
        let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_elseSeq_2315_);
        v___x_2329_ = l_Lean_Elab_Do_elabDoSeq(
            v_thenSeq_2317_,
            v_dec_2316_,
            v___x_2327_,
            v___y_2319_,
            v___y_2320_,
            v___y_2321_,
            v___y_2322_,
            v___y_2323_,
            v___y_2324_,
            v___y_2325_,
        );
        return v___x_2329_;
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(
    mut v_elseSeq_2330_: *mut crate::leanh::LeanObject,
    mut v_dec_2331_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2332_: *mut crate::leanh::LeanObject,
    mut v_then___2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_then___00boxed_2342_: u8 = 0;
    let mut v_res_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_then___00boxed_2342_ = (crate::leanh::lean_unbox(v_then___2333_) as u8);
    v_res_2343_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(
        v_elseSeq_2330_,
        v_dec_2331_,
        v_thenSeq_2332_,
        v_then___00boxed_2342_,
        v___y_2334_,
        v___y_2335_,
        v___y_2336_,
        v___y_2337_,
        v___y_2338_,
        v___y_2339_,
        v___y_2340_,
    );
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    crate::leanh::lean_dec(v___y_2338_);
    crate::leanh::lean_dec_ref(v___y_2337_);
    crate::leanh::lean_dec(v___y_2336_);
    crate::leanh::lean_dec_ref(v___y_2335_);
    crate::leanh::lean_dec_ref(v___y_2334_);
    return v_res_2343_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(
    mut v_h_2355_: *mut crate::leanh::LeanObject,
    mut v_cond_2356_: *mut crate::leanh::LeanObject,
    mut v_then___2357_: *mut crate::leanh::LeanObject,
    mut v___x_2358_: u8,
    mut v_else___2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doBlockResultType_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doBlockResultType_2368_ = crate::leanh::lean_ctor_get(v___y_2360_, 3);
                crate::leanh::lean_inc_ref(v_doBlockResultType_2368_);
                v___x_2369_ = l_Lean_Elab_Do_mkMonadApp(
                    v_doBlockResultType_2368_,
                    v___y_2360_,
                    v___y_2361_,
                    v___y_2362_,
                    v___y_2363_,
                    v___y_2364_,
                    v___y_2365_,
                    v___y_2366_,
                );
                if crate::leanh::lean_obj_tag(v___x_2369_) == 0 {
                    v_a_2370_ = crate::leanh::lean_ctor_get(v___x_2369_, 0);
                    v_isSharedCheck_2424_ = (!crate::leanh::lean_is_exclusive(v___x_2369_)) as u8;
                    if v_isSharedCheck_2424_ == 0 {
                        v___x_2372_ = v___x_2369_;
                        v_isShared_2373_ = v_isSharedCheck_2424_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2370_);
                        crate::leanh::lean_dec(v___x_2369_);
                        v___x_2372_ = crate::leanh::lean_box(0);
                        v_isShared_2373_ = v_isSharedCheck_2424_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_else___2359_);
                    crate::leanh::lean_dec(v_then___2357_);
                    crate::leanh::lean_dec(v_cond_2356_);
                    crate::leanh::lean_dec(v_h_2355_);
                    return v___x_2369_;
                }
            }
            1 => {
                v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35;
                crate::leanh::lean_inc(v_h_2355_);
                v___x_2375_ = l_Lean_Syntax_isOfKind(v_h_2355_, v___x_2374_);
                if v___x_2375_ == 0 {
                    v___x_2376_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1;
                    crate::leanh::lean_inc(v_h_2355_);
                    v___x_2377_ = l_Lean_Syntax_isOfKind(v_h_2355_, v___x_2376_);
                    if v___x_2377_ == 0 {
                        crate::leanh::lean_del_object(v___x_2372_);
                        crate::leanh::lean_dec(v_a_2370_);
                        crate::leanh::lean_dec(v_else___2359_);
                        crate::leanh::lean_dec(v_then___2357_);
                        crate::leanh::lean_dec(v_cond_2356_);
                        crate::leanh::lean_dec(v_h_2355_);
                        v___x_2378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
                        return v___x_2378_;
                    } else {
                        v_ref_2379_ = crate::leanh::lean_ctor_get(v___y_2365_, 5);
                        v___x_2380_ = l_Lean_SourceInfo_fromRef(v_ref_2379_, v___x_2375_);
                        v___x_2381_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3;
                        v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9;
                        crate::leanh::lean_inc_n(v___x_2380_, 5);
                        v___x_2383_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2380_);
                        crate::leanh::lean_ctor_set(v___x_2383_, 1, v___x_2382_);
                        v___x_2384_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5;
                        v___x_2385_ = l_Lean_Syntax_node1(v___x_2380_, v___x_2384_, v_h_2355_);
                        v___x_2386_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6;
                        v___x_2387_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2380_);
                        crate::leanh::lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                        v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10;
                        v___x_2389_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2389_, 0, v___x_2380_);
                        crate::leanh::lean_ctor_set(v___x_2389_, 1, v___x_2388_);
                        v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14;
                        v___x_2391_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2391_, 0, v___x_2380_);
                        crate::leanh::lean_ctor_set(v___x_2391_, 1, v___x_2390_);
                        v___x_2392_ = l_Lean_Syntax_node8(
                            v___x_2380_,
                            v___x_2381_,
                            v___x_2383_,
                            v___x_2385_,
                            v___x_2387_,
                            v_cond_2356_,
                            v___x_2389_,
                            v_then___2357_,
                            v___x_2391_,
                            v_else___2359_,
                        );
                        if v_isShared_2373_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2372_, 1);
                            v___x_2394_ = v___x_2372_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2397_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2370_);
                            v___x_2394_ = v_reuseFailAlloc_2397_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_ref_2398_ = crate::leanh::lean_ctor_get(v___y_2365_, 5);
                    v___x_2399_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2400_ = l_Lean_Syntax_getArg(v_h_2355_, v___x_2399_);
                    crate::leanh::lean_dec(v_h_2355_);
                    v___x_2401_ = 0;
                    v___x_2402_ = l_Lean_SourceInfo_fromRef(v_ref_2398_, v___x_2401_);
                    v___x_2403_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3;
                    v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9;
                    crate::leanh::lean_inc_n(v___x_2402_, 6);
                    v___x_2405_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2402_);
                    crate::leanh::lean_ctor_set(v___x_2405_, 1, v___x_2404_);
                    v___x_2406_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5;
                    v___x_2407_ = l_Lean_SourceInfo_fromRef(v___x_2400_, v___x_2358_);
                    crate::leanh::lean_dec(v___x_2400_);
                    v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36;
                    v___x_2409_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2409_, 0, v___x_2407_);
                    crate::leanh::lean_ctor_set(v___x_2409_, 1, v___x_2408_);
                    v___x_2410_ = l_Lean_Syntax_node1(v___x_2402_, v___x_2374_, v___x_2409_);
                    v___x_2411_ = l_Lean_Syntax_node1(v___x_2402_, v___x_2406_, v___x_2410_);
                    v___x_2412_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6;
                    v___x_2413_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2413_, 0, v___x_2402_);
                    crate::leanh::lean_ctor_set(v___x_2413_, 1, v___x_2412_);
                    v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10;
                    v___x_2415_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2415_, 0, v___x_2402_);
                    crate::leanh::lean_ctor_set(v___x_2415_, 1, v___x_2414_);
                    v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14;
                    v___x_2417_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2402_);
                    crate::leanh::lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                    v___x_2418_ = l_Lean_Syntax_node8(
                        v___x_2402_,
                        v___x_2403_,
                        v___x_2405_,
                        v___x_2411_,
                        v___x_2413_,
                        v_cond_2356_,
                        v___x_2415_,
                        v_then___2357_,
                        v___x_2417_,
                        v_else___2359_,
                    );
                    if v_isShared_2373_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2372_, 1);
                        v___x_2420_ = v___x_2372_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2370_);
                        v___x_2420_ = v_reuseFailAlloc_2423_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2395_ = crate::leanh::lean_box(0);
                v___x_2396_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_2392_,
                    v___x_2394_,
                    v___x_2358_,
                    v___x_2358_,
                    v___x_2395_,
                    v___y_2361_,
                    v___y_2362_,
                    v___y_2363_,
                    v___y_2364_,
                    v___y_2365_,
                    v___y_2366_,
                );
                return v___x_2396_;
            }
            3 => {
                v___x_2421_ = crate::leanh::lean_box(0);
                v___x_2422_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_2418_,
                    v___x_2420_,
                    v___x_2358_,
                    v___x_2358_,
                    v___x_2421_,
                    v___y_2361_,
                    v___y_2362_,
                    v___y_2363_,
                    v___y_2364_,
                    v___y_2365_,
                    v___y_2366_,
                );
                return v___x_2422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(
    mut v_h_2425_: *mut crate::leanh::LeanObject,
    mut v_cond_2426_: *mut crate::leanh::LeanObject,
    mut v_then___2427_: *mut crate::leanh::LeanObject,
    mut v___x_2428_: *mut crate::leanh::LeanObject,
    mut v_else___2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7828__boxed_2438_: u8 = 0;
    let mut v_res_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7828__boxed_2438_ = (crate::leanh::lean_unbox(v___x_2428_) as u8);
    v_res_2439_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(
        v_h_2425_,
        v_cond_2426_,
        v_then___2427_,
        v___x_7828__boxed_2438_,
        v_else___2429_,
        v___y_2430_,
        v___y_2431_,
        v___y_2432_,
        v___y_2433_,
        v___y_2434_,
        v___y_2435_,
        v___y_2436_,
    );
    crate::leanh::lean_dec(v___y_2436_);
    crate::leanh::lean_dec_ref(v___y_2435_);
    crate::leanh::lean_dec(v___y_2434_);
    crate::leanh::lean_dec_ref(v___y_2433_);
    crate::leanh::lean_dec(v___y_2432_);
    crate::leanh::lean_dec_ref(v___y_2431_);
    crate::leanh::lean_dec_ref(v___y_2430_);
    return v_res_2439_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(
    mut v_h_2440_: *mut crate::leanh::LeanObject,
    mut v_cond_2441_: *mut crate::leanh::LeanObject,
    mut v___x_2442_: u8,
    mut v_elabDiteBranch_2443_: *mut crate::leanh::LeanObject,
    mut v_then___2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
    mut v___y_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = crate::leanh::lean_box((v___x_2442_) as usize);
    v___f_2454_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed
            as *mut core::ffi::c_void,
        13,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2454_, 0, v_h_2440_);
    crate::leanh::lean_closure_set(v___f_2454_, 1, v_cond_2441_);
    crate::leanh::lean_closure_set(v___f_2454_, 2, v_then___2444_);
    crate::leanh::lean_closure_set(v___f_2454_, 3, v___x_2453_);
    v___x_2455_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once), _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
    v___x_2456_ = 0;
    v___x_2457_ = crate::leanh::lean_box((v___x_2456_) as usize);
    v___x_2458_ = crate::leanh::lean_apply_1(v_elabDiteBranch_2443_, v___x_2457_);
    v___x_2459_ = crate::leanh::lean_box(0);
    v___x_2460_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
        v___x_2455_,
        v___x_2458_,
        v___f_2454_,
        v___x_2459_,
        v___y_2445_,
        v___y_2446_,
        v___y_2447_,
        v___y_2448_,
        v___y_2449_,
        v___y_2450_,
        v___y_2451_,
    );
    return v___x_2460_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(
    mut v_h_2461_: *mut crate::leanh::LeanObject,
    mut v_cond_2462_: *mut crate::leanh::LeanObject,
    mut v___x_2463_: *mut crate::leanh::LeanObject,
    mut v_elabDiteBranch_2464_: *mut crate::leanh::LeanObject,
    mut v_then___2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7980__boxed_2474_: u8 = 0;
    let mut v_res_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7980__boxed_2474_ = (crate::leanh::lean_unbox(v___x_2463_) as u8);
    v_res_2475_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(
        v_h_2461_,
        v_cond_2462_,
        v___x_7980__boxed_2474_,
        v_elabDiteBranch_2464_,
        v_then___2465_,
        v___y_2466_,
        v___y_2467_,
        v___y_2468_,
        v___y_2469_,
        v___y_2470_,
        v___y_2471_,
        v___y_2472_,
    );
    crate::leanh::lean_dec(v___y_2472_);
    crate::leanh::lean_dec_ref(v___y_2471_);
    crate::leanh::lean_dec(v___y_2470_);
    crate::leanh::lean_dec_ref(v___y_2469_);
    crate::leanh::lean_dec(v___y_2468_);
    crate::leanh::lean_dec_ref(v___y_2467_);
    crate::leanh::lean_dec_ref(v___y_2466_);
    return v_res_2475_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(
    mut v_h_2476_: *mut crate::leanh::LeanObject,
    mut v_cond_2477_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2478_: *mut crate::leanh::LeanObject,
    mut v_elseSeq_2479_: *mut crate::leanh::LeanObject,
    mut v_dec_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
    mut v_a_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elabDiteBranch_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_thenSeq_2478_);
    crate::leanh::lean_inc_ref(v_dec_2480_);
    crate::leanh::lean_inc(v_elseSeq_2479_);
    v_elabDiteBranch_2489_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        3,
    );
    crate::leanh::lean_closure_set(v_elabDiteBranch_2489_, 0, v_elseSeq_2479_);
    crate::leanh::lean_closure_set(v_elabDiteBranch_2489_, 1, v_dec_2480_);
    crate::leanh::lean_closure_set(v_elabDiteBranch_2489_, 2, v_thenSeq_2478_);
    v___x_2490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once
        ),
        _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2,
    );
    v___x_2491_ = 1;
    v___x_2492_ = crate::leanh::lean_box((v___x_2491_) as usize);
    v___f_2493_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed
            as *mut core::ffi::c_void,
        13,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2493_, 0, v_h_2476_);
    crate::leanh::lean_closure_set(v___f_2493_, 1, v_cond_2477_);
    crate::leanh::lean_closure_set(v___f_2493_, 2, v___x_2492_);
    crate::leanh::lean_closure_set(v___f_2493_, 3, v_elabDiteBranch_2489_);
    v___x_2494_ = crate::leanh::lean_box((v___x_2491_) as usize);
    v___x_2495_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        4,
    );
    crate::leanh::lean_closure_set(v___x_2495_, 0, v_elseSeq_2479_);
    crate::leanh::lean_closure_set(v___x_2495_, 1, v_dec_2480_);
    crate::leanh::lean_closure_set(v___x_2495_, 2, v_thenSeq_2478_);
    crate::leanh::lean_closure_set(v___x_2495_, 3, v___x_2494_);
    v___x_2496_ = crate::leanh::lean_box(0);
    v___x_2497_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
        v___x_2490_,
        v___x_2495_,
        v___f_2493_,
        v___x_2496_,
        v_a_2481_,
        v_a_2482_,
        v_a_2483_,
        v_a_2484_,
        v_a_2485_,
        v_a_2486_,
        v_a_2487_,
    );
    return v___x_2497_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(
    mut v_h_2498_: *mut crate::leanh::LeanObject,
    mut v_cond_2499_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2500_: *mut crate::leanh::LeanObject,
    mut v_elseSeq_2501_: *mut crate::leanh::LeanObject,
    mut v_dec_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2511_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(
        v_h_2498_,
        v_cond_2499_,
        v_thenSeq_2500_,
        v_elseSeq_2501_,
        v_dec_2502_,
        v_a_2503_,
        v_a_2504_,
        v_a_2505_,
        v_a_2506_,
        v_a_2507_,
        v_a_2508_,
        v_a_2509_,
    );
    crate::leanh::lean_dec(v_a_2509_);
    crate::leanh::lean_dec_ref(v_a_2508_);
    crate::leanh::lean_dec(v_a_2507_);
    crate::leanh::lean_dec_ref(v_a_2506_);
    crate::leanh::lean_dec(v_a_2505_);
    crate::leanh::lean_dec_ref(v_a_2504_);
    crate::leanh::lean_dec_ref(v_a_2503_);
    return v_res_2511_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoIf___lam__0(
    mut v___x_2512_: *mut crate::leanh::LeanObject,
    mut v___x_2513_: *mut crate::leanh::LeanObject,
    mut v___x_2514_: *mut crate::leanh::LeanObject,
    mut v___x_2515_: *mut crate::leanh::LeanObject,
    mut v___x_2516_: *mut crate::leanh::LeanObject,
    mut v___x_2517_: *mut crate::leanh::LeanObject,
    mut v___x_2518_: *mut crate::leanh::LeanObject,
    mut v_thenSeq_2519_: *mut crate::leanh::LeanObject,
    mut v_elseSeq_2520_: *mut crate::leanh::LeanObject,
    mut v_dec_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7;
    v___x_2531_ = l_Lean_Name_mkStr4(v___x_2512_, v___x_2513_, v___x_2514_, v___x_2530_);
    crate::leanh::lean_inc(v___x_2515_);
    v___x_2532_ = l_Lean_Syntax_isOfKind(v___x_2515_, v___x_2531_);
    crate::leanh::lean_dec(v___x_2531_);
    if v___x_2532_ == 0 {
        let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_dec_2521_);
        crate::leanh::lean_dec(v_elseSeq_2520_);
        crate::leanh::lean_dec(v_thenSeq_2519_);
        crate::leanh::lean_dec(v___x_2515_);
        v___x_2533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
        return v___x_2533_;
    } else {
        let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2535_: u8 = 0;
        v___x_2534_ = l_Lean_Syntax_getArg(v___x_2515_, v___x_2516_);
        crate::leanh::lean_inc(v___x_2534_);
        v___x_2535_ = l_Lean_Syntax_matchesNull(v___x_2534_, v___x_2516_);
        if v___x_2535_ == 0 {
            let mut v___x_2536_: u8 = 0;
            crate::leanh::lean_inc(v___x_2534_);
            v___x_2536_ = l_Lean_Syntax_matchesNull(v___x_2534_, v___x_2517_);
            if v___x_2536_ == 0 {
                let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2534_);
                crate::leanh::lean_dec_ref(v_dec_2521_);
                crate::leanh::lean_dec(v_elseSeq_2520_);
                crate::leanh::lean_dec(v_thenSeq_2519_);
                crate::leanh::lean_dec(v___x_2515_);
                v___x_2537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
                return v___x_2537_;
            } else {
                let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2538_ = l_Lean_Syntax_getArg(v___x_2534_, v___x_2516_);
                crate::leanh::lean_dec(v___x_2534_);
                v___x_2539_ = l_Lean_Syntax_getArg(v___x_2515_, v___x_2518_);
                crate::leanh::lean_dec(v___x_2515_);
                v___x_2540_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(
                    v___x_2538_,
                    v___x_2539_,
                    v_thenSeq_2519_,
                    v_elseSeq_2520_,
                    v_dec_2521_,
                    v___y_2522_,
                    v___y_2523_,
                    v___y_2524_,
                    v___y_2525_,
                    v___y_2526_,
                    v___y_2527_,
                    v___y_2528_,
                );
                return v___x_2540_;
            }
        } else {
            let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2534_);
            v___x_2541_ = l_Lean_Syntax_getArg(v___x_2515_, v___x_2518_);
            crate::leanh::lean_dec(v___x_2515_);
            v___x_2542_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(
                v___x_2541_,
                v_thenSeq_2519_,
                v_elseSeq_2520_,
                v_dec_2521_,
                v___y_2522_,
                v___y_2523_,
                v___y_2524_,
                v___y_2525_,
                v___y_2526_,
                v___y_2527_,
                v___y_2528_,
            );
            return v___x_2542_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoIf___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2543_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2544_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2545_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2546_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2547_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2548_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2549_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_thenSeq_2550_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_elseSeq_2551_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_dec_2552_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2553_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2554_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2555_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2556_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2557_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2558_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2559_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2560_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Lean_Elab_Do_elabDoIf___lam__0(
        v___x_2543_,
        v___x_2544_,
        v___x_2545_,
        v___x_2546_,
        v___x_2547_,
        v___x_2548_,
        v___x_2549_,
        v_thenSeq_2550_,
        v_elseSeq_2551_,
        v_dec_2552_,
        v___y_2553_,
        v___y_2554_,
        v___y_2555_,
        v___y_2556_,
        v___y_2557_,
        v___y_2558_,
        v___y_2559_,
    );
    crate::leanh::lean_dec(v___y_2559_);
    crate::leanh::lean_dec_ref(v___y_2558_);
    crate::leanh::lean_dec(v___y_2557_);
    crate::leanh::lean_dec_ref(v___y_2556_);
    crate::leanh::lean_dec(v___y_2555_);
    crate::leanh::lean_dec_ref(v___y_2554_);
    crate::leanh::lean_dec_ref(v___y_2553_);
    crate::leanh::lean_dec(v___x_2549_);
    crate::leanh::lean_dec(v___x_2548_);
    crate::leanh::lean_dec(v___x_2547_);
    return v_res_2561_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoIf(
    mut v_stx_2562_: *mut crate::leanh::LeanObject,
    mut v_dec_2563_: *mut crate::leanh::LeanObject,
    mut v_a_2564_: *mut crate::leanh::LeanObject,
    mut v_a_2565_: *mut crate::leanh::LeanObject,
    mut v_a_2566_: *mut crate::leanh::LeanObject,
    mut v_a_2567_: *mut crate::leanh::LeanObject,
    mut v_a_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
    mut v_a_2570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thenSeq_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elseSeq_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v_a_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0;
                v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1;
                v___x_2574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2;
                v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4;
                crate::leanh::lean_inc(v_stx_2562_);
                v___x_2576_ = l_Lean_Syntax_isOfKind(v_stx_2562_, v___x_2575_);
                if v___x_2576_ == 0 {
                    crate::leanh::lean_dec_ref(v_dec_2563_);
                    crate::leanh::lean_dec(v_stx_2562_);
                    v___x_2577_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
                    return v___x_2577_;
                } else {
                    v___x_2578_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2579_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2580_ = l_Lean_Syntax_getArg(v_stx_2562_, v___x_2579_);
                    v___x_2581_ = l_Lean_Syntax_matchesNull(v___x_2580_, v___x_2578_);
                    if v___x_2581_ == 0 {
                        crate::leanh::lean_dec_ref(v_dec_2563_);
                        crate::leanh::lean_dec(v_stx_2562_);
                        v___x_2582_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
                        return v___x_2582_;
                    } else {
                        v___x_2583_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2584_ = crate::leanh::lean_unsigned_to_nat(5);
                        v___x_2585_ = l_Lean_Syntax_getArg(v_stx_2562_, v___x_2584_);
                        crate::leanh::lean_inc(v___x_2585_);
                        v___x_2586_ = l_Lean_Syntax_matchesNull(v___x_2585_, v___x_2583_);
                        if v___x_2586_ == 0 {
                            crate::leanh::lean_dec(v___x_2585_);
                            crate::leanh::lean_dec_ref(v_dec_2563_);
                            crate::leanh::lean_dec(v_stx_2562_);
                            v___x_2587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
                            return v___x_2587_;
                        } else {
                            v___x_2588_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_thenSeq_2589_ = l_Lean_Syntax_getArg(v_stx_2562_, v___x_2588_);
                            crate::leanh::lean_inc(v_thenSeq_2589_);
                            v___x_2590_ = l_Lean_Elab_Do_inferControlInfoSeq(
                                v_thenSeq_2589_,
                                v_a_2565_,
                                v_a_2566_,
                                v_a_2567_,
                                v_a_2568_,
                                v_a_2569_,
                                v_a_2570_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2590_) == 0 {
                                v_a_2591_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                                crate::leanh::lean_inc(v_a_2591_);
                                crate::leanh::lean_dec_ref_known(v___x_2590_, 1);
                                v___x_2592_ = crate::leanh::lean_unsigned_to_nat(1);
                                v_elseSeq_2593_ = l_Lean_Syntax_getArg(v___x_2585_, v___x_2592_);
                                crate::leanh::lean_dec(v___x_2585_);
                                crate::leanh::lean_inc(v_elseSeq_2593_);
                                v___x_2594_ = l_Lean_Elab_Do_inferControlInfoSeq(
                                    v_elseSeq_2593_,
                                    v_a_2565_,
                                    v_a_2566_,
                                    v_a_2567_,
                                    v_a_2568_,
                                    v_a_2569_,
                                    v_a_2570_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2594_) == 0 {
                                    v_a_2595_ = crate::leanh::lean_ctor_get(v___x_2594_, 0);
                                    crate::leanh::lean_inc(v_a_2595_);
                                    crate::leanh::lean_dec_ref_known(v___x_2594_, 1);
                                    v___x_2596_ = l_Lean_Syntax_getArg(v_stx_2562_, v___x_2592_);
                                    crate::leanh::lean_dec(v_stx_2562_);
                                    v___f_2597_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_Do_elabDoIf___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        18,
                                        9,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2597_, 0, v___x_2572_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 1, v___x_2573_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 2, v___x_2574_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 3, v___x_2596_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 4, v___x_2578_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 5, v___x_2583_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 6, v___x_2592_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 7, v_thenSeq_2589_);
                                    crate::leanh::lean_closure_set(v___f_2597_, 8, v_elseSeq_2593_);
                                    v___x_2598_ = l_Lean_Elab_Do_ControlInfo_alternative(
                                        v_a_2591_, v_a_2595_,
                                    );
                                    v___x_2599_ = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(
                                        v_dec_2563_,
                                        v___x_2598_,
                                        v___f_2597_,
                                        v_a_2564_,
                                        v_a_2565_,
                                        v_a_2566_,
                                        v_a_2567_,
                                        v_a_2568_,
                                        v_a_2569_,
                                        v_a_2570_,
                                    );
                                    return v___x_2599_;
                                } else {
                                    crate::leanh::lean_dec(v_elseSeq_2593_);
                                    crate::leanh::lean_dec(v_a_2591_);
                                    crate::leanh::lean_dec(v_thenSeq_2589_);
                                    crate::leanh::lean_dec_ref(v_dec_2563_);
                                    crate::leanh::lean_dec(v_stx_2562_);
                                    v_a_2600_ = crate::leanh::lean_ctor_get(v___x_2594_, 0);
                                    v_isSharedCheck_2607_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2594_)) as u8;
                                    if v_isSharedCheck_2607_ == 0 {
                                        v___x_2602_ = v___x_2594_;
                                        v_isShared_2603_ = v_isSharedCheck_2607_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2600_);
                                        crate::leanh::lean_dec(v___x_2594_);
                                        v___x_2602_ = crate::leanh::lean_box(0);
                                        v_isShared_2603_ = v_isSharedCheck_2607_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_thenSeq_2589_);
                                crate::leanh::lean_dec(v___x_2585_);
                                crate::leanh::lean_dec_ref(v_dec_2563_);
                                crate::leanh::lean_dec(v_stx_2562_);
                                v_a_2608_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                                v_isSharedCheck_2615_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2590_)) as u8;
                                if v_isSharedCheck_2615_ == 0 {
                                    v___x_2610_ = v___x_2590_;
                                    v_isShared_2611_ = v_isSharedCheck_2615_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2608_);
                                    crate::leanh::lean_dec(v___x_2590_);
                                    v___x_2610_ = crate::leanh::lean_box(0);
                                    v_isShared_2611_ = v_isSharedCheck_2615_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2603_ == 0 {
                    v___x_2605_ = v___x_2602_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
                    v___x_2605_ = v_reuseFailAlloc_2606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2605_;
            }
            3 => {
                if v_isShared_2611_ == 0 {
                    v___x_2613_ = v___x_2610_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
                    v___x_2613_ = v_reuseFailAlloc_2614_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoIf___boxed(
    mut v_stx_2616_: *mut crate::leanh::LeanObject,
    mut v_dec_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2626_ = l_Lean_Elab_Do_elabDoIf(
        v_stx_2616_,
        v_dec_2617_,
        v_a_2618_,
        v_a_2619_,
        v_a_2620_,
        v_a_2621_,
        v_a_2622_,
        v_a_2623_,
        v_a_2624_,
    );
    crate::leanh::lean_dec(v_a_2624_);
    crate::leanh::lean_dec_ref(v_a_2623_);
    crate::leanh::lean_dec(v_a_2622_);
    crate::leanh::lean_dec_ref(v_a_2621_);
    crate::leanh::lean_dec(v_a_2620_);
    crate::leanh::lean_dec_ref(v_a_2619_);
    crate::leanh::lean_dec_ref(v_a_2618_);
    return v_res_2626_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2634_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4;
    v___x_2636_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1;
    v___x_2637_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoIf___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2638_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2634_,
        v___x_2635_,
        v___x_2636_,
        v___x_2637_,
    );
    return v___x_2638_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(
    mut v_a_2639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2640_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
    return v_res_2640_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_If(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_If(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_If(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_If(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_If(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_If(builtin);
}
