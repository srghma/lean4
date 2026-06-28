// Lean compiler output
// Module: Lean.Elab.Command.WithWeakNamespace
// Imports: Lean.Elab.Command
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_elabCommand___boxed, l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Elab_Command_modifyScope___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Namespace::l_Lean_Environment_registerNamespace;
use crate::lean_imports_rs::Init::Prelude::lean_string_dec_eq;
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [95, 114, 111, 111, 116, 95, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [119, 105, 116, 104, 87, 101, 97, 107, 78, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3_value) as *mut LeanObject,17255988671739451913 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value) as *mut LeanObject,372336756845014741 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [87, 105, 116, 104, 87, 101, 97, 107, 78, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6_value) as *mut LeanObject,10127352484326591666 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,1021896329494142643 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value) as *mut LeanObject,8226412675986123934 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value) as *mut LeanObject,6019352646893511020 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value) as *mut LeanObject,5635997962862644633 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 87, 105, 116, 104, 87, 101, 97, 107, 78, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12_value) as *mut LeanObject,10212291502915676414 as *mut LeanObject] };
static mut l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(
    mut v_ns_263_: *mut LeanObject,
    mut v_x_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pre_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: u8 = 0;
    let mut v_pre_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_264_) {
                0 => {
                    lean_inc(v_ns_263_);
                    return v_ns_263_;
                }
                1 => {
                    v_pre_265_ = lean_ctor_get(v_x_264_, 0);
                    lean_inc(v_pre_265_);
                    v_str_266_ = lean_ctor_get(v_x_264_, 1);
                    lean_inc_ref(v_str_266_);
                    lean_dec_ref_known(v_x_264_, 2);
                    if lean_obj_tag(v_pre_265_) == 0 {
                        v___x_270_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0;
                        v___x_271_ = lean_string_dec_eq(v_str_266_, v___x_270_);
                        if v___x_271_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_str_266_);
                            return v_pre_265_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_pre_272_ = lean_ctor_get(v_x_264_, 0);
                    lean_inc(v_pre_272_);
                    v_i_273_ = lean_ctor_get(v_x_264_, 1);
                    lean_inc(v_i_273_);
                    lean_dec_ref_known(v_x_264_, 2);
                    v___x_274_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_ns_263_, v_pre_272_);
                    v___x_275_ = l_Lean_Name_num___override(v___x_274_, v_i_273_);
                    return v___x_275_;
                }
            },
            1 => {
                v___x_268_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_ns_263_, v_pre_265_);
                v___x_269_ = l_Lean_Name_str___override(v___x_268_, v_str_266_);
                return v___x_269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___boxed(
    mut v_ns_276_: *mut LeanObject,
    mut v_x_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_ns_276_, v_x_277_);
    lean_dec(v_ns_276_);
    return v_res_278_;
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__0(
    mut v___x_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_header_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelNames_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varDecls_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varUIds_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includedVars_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_289_: u8 = 0;
    let mut v_isPublic_290_: u8 = 0;
    let mut v_isMeta_291_: u8 = 0;
    let mut v_attrs_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut v_unused_300_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_281_ = lean_ctor_get(v_x_280_, 0);
                v_opts_282_ = lean_ctor_get(v_x_280_, 1);
                v_openDecls_283_ = lean_ctor_get(v_x_280_, 3);
                v_levelNames_284_ = lean_ctor_get(v_x_280_, 4);
                v_varDecls_285_ = lean_ctor_get(v_x_280_, 5);
                v_varUIds_286_ = lean_ctor_get(v_x_280_, 6);
                v_includedVars_287_ = lean_ctor_get(v_x_280_, 7);
                v_omittedVars_288_ = lean_ctor_get(v_x_280_, 8);
                v_isNoncomputable_289_ = lean_ctor_get_uint8(
                    v_x_280_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isPublic_290_ = lean_ctor_get_uint8(
                    v_x_280_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_291_ = lean_ctor_get_uint8(
                    v_x_280_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_292_ = lean_ctor_get(v_x_280_, 9);
                v_isSharedCheck_299_ = (!lean_is_exclusive(v_x_280_)) as u8;
                if v_isSharedCheck_299_ == 0 {
                    v_unused_300_ = lean_ctor_get(v_x_280_, 2);
                    lean_dec(v_unused_300_);
                    v___x_294_ = v_x_280_;
                    v_isShared_295_ = v_isSharedCheck_299_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_attrs_292_);
                    lean_inc(v_omittedVars_288_);
                    lean_inc(v_includedVars_287_);
                    lean_inc(v_varUIds_286_);
                    lean_inc(v_varDecls_285_);
                    lean_inc(v_levelNames_284_);
                    lean_inc(v_openDecls_283_);
                    lean_inc(v_opts_282_);
                    lean_inc(v_header_281_);
                    lean_dec(v_x_280_);
                    v___x_294_ = lean_box(0);
                    v_isShared_295_ = v_isSharedCheck_299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_295_ == 0 {
                    lean_ctor_set(v___x_294_, 2, v___x_279_);
                    v___x_297_ = v___x_294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 10, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_298_, 0, v_header_281_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 1, v_opts_282_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 2, v___x_279_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 3, v_openDecls_283_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 4, v_levelNames_284_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 5, v_varDecls_285_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 6, v_varUIds_286_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 7, v_includedVars_287_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 8, v_omittedVars_288_);
                    lean_ctor_set(v_reuseFailAlloc_298_, 9, v_attrs_292_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_298_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_isNoncomputable_289_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_298_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                        v_isPublic_290_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_298_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                        v_isMeta_291_,
                    );
                    v___x_297_ = v_reuseFailAlloc_298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__1(
    mut v_currNamespace_301_: *mut LeanObject,
    mut v_x_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_header_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelNames_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varDecls_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varUIds_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includedVars_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_311_: u8 = 0;
    let mut v_isPublic_312_: u8 = 0;
    let mut v_isMeta_313_: u8 = 0;
    let mut v_attrs_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_317_: u8 = 0;
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_321_: u8 = 0;
    let mut v_unused_322_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_303_ = lean_ctor_get(v_x_302_, 0);
                v_opts_304_ = lean_ctor_get(v_x_302_, 1);
                v_openDecls_305_ = lean_ctor_get(v_x_302_, 3);
                v_levelNames_306_ = lean_ctor_get(v_x_302_, 4);
                v_varDecls_307_ = lean_ctor_get(v_x_302_, 5);
                v_varUIds_308_ = lean_ctor_get(v_x_302_, 6);
                v_includedVars_309_ = lean_ctor_get(v_x_302_, 7);
                v_omittedVars_310_ = lean_ctor_get(v_x_302_, 8);
                v_isNoncomputable_311_ = lean_ctor_get_uint8(
                    v_x_302_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isPublic_312_ = lean_ctor_get_uint8(
                    v_x_302_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_313_ = lean_ctor_get_uint8(
                    v_x_302_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_314_ = lean_ctor_get(v_x_302_, 9);
                v_isSharedCheck_321_ = (!lean_is_exclusive(v_x_302_)) as u8;
                if v_isSharedCheck_321_ == 0 {
                    v_unused_322_ = lean_ctor_get(v_x_302_, 2);
                    lean_dec(v_unused_322_);
                    v___x_316_ = v_x_302_;
                    v_isShared_317_ = v_isSharedCheck_321_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_attrs_314_);
                    lean_inc(v_omittedVars_310_);
                    lean_inc(v_includedVars_309_);
                    lean_inc(v_varUIds_308_);
                    lean_inc(v_varDecls_307_);
                    lean_inc(v_levelNames_306_);
                    lean_inc(v_openDecls_305_);
                    lean_inc(v_opts_304_);
                    lean_inc(v_header_303_);
                    lean_dec(v_x_302_);
                    v___x_316_ = lean_box(0);
                    v_isShared_317_ = v_isSharedCheck_321_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_317_ == 0 {
                    lean_ctor_set(v___x_316_, 2, v_currNamespace_301_);
                    v___x_319_ = v___x_316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 10, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_320_, 0, v_header_303_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 1, v_opts_304_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 2, v_currNamespace_301_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 3, v_openDecls_305_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 4, v_levelNames_306_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 5, v_varDecls_307_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 6, v_varUIds_308_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 7, v_includedVars_309_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 8, v_omittedVars_310_);
                    lean_ctor_set(v_reuseFailAlloc_320_, 9, v_attrs_314_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_320_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_isNoncomputable_311_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_320_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                        v_isPublic_312_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_320_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                        v_isMeta_313_,
                    );
                    v___x_319_ = v_reuseFailAlloc_320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(
    mut v_ns_323_: *mut LeanObject,
    mut v_m_324_: *mut LeanObject,
    mut v_a_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_359_: u8 = 0;
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_363_: u8 = 0;
    let mut v_unused_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_368_: u8 = 0;
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_372_: u8 = 0;
    let mut v_a_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_377_: u8 = 0;
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_381_: u8 = 0;
    let mut v_unused_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_386_: u8 = 0;
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_390_: u8 = 0;
    let mut v_a_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_394_: u8 = 0;
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_398_: u8 = 0;
    let mut v_reuseFailAlloc_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_400_: u8 = 0;
    let mut v_a_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_404_: u8 = 0;
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_328_ = l_Lean_Elab_Command_getScope___redArg(v_a_326_);
                if lean_obj_tag(v___x_328_) == 0 {
                    v_a_329_ = lean_ctor_get(v___x_328_, 0);
                    lean_inc(v_a_329_);
                    lean_dec_ref_known(v___x_328_, 1);
                    v___x_330_ = lean_st_ref_take(v_a_326_);
                    v_currNamespace_331_ = lean_ctor_get(v_a_329_, 2);
                    lean_inc(v_currNamespace_331_);
                    lean_dec(v_a_329_);
                    v_env_332_ = lean_ctor_get(v___x_330_, 0);
                    v_messages_333_ = lean_ctor_get(v___x_330_, 1);
                    v_scopes_334_ = lean_ctor_get(v___x_330_, 2);
                    v_usedQuotCtxts_335_ = lean_ctor_get(v___x_330_, 3);
                    v_nextMacroScope_336_ = lean_ctor_get(v___x_330_, 4);
                    v_maxRecDepth_337_ = lean_ctor_get(v___x_330_, 5);
                    v_ngen_338_ = lean_ctor_get(v___x_330_, 6);
                    v_auxDeclNGen_339_ = lean_ctor_get(v___x_330_, 7);
                    v_infoState_340_ = lean_ctor_get(v___x_330_, 8);
                    v_traceState_341_ = lean_ctor_get(v___x_330_, 9);
                    v_snapshotTasks_342_ = lean_ctor_get(v___x_330_, 10);
                    v_isSharedCheck_400_ = (!lean_is_exclusive(v___x_330_)) as u8;
                    if v_isSharedCheck_400_ == 0 {
                        v___x_344_ = v___x_330_;
                        v_isShared_345_ = v_isSharedCheck_400_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_342_);
                        lean_inc(v_traceState_341_);
                        lean_inc(v_infoState_340_);
                        lean_inc(v_auxDeclNGen_339_);
                        lean_inc(v_ngen_338_);
                        lean_inc(v_maxRecDepth_337_);
                        lean_inc(v_nextMacroScope_336_);
                        lean_inc(v_usedQuotCtxts_335_);
                        lean_inc(v_scopes_334_);
                        lean_inc(v_messages_333_);
                        lean_inc(v_env_332_);
                        lean_dec(v___x_330_);
                        v___x_344_ = lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_400_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_m_324_);
                    lean_dec(v_ns_323_);
                    v_a_401_ = lean_ctor_get(v___x_328_, 0);
                    v_isSharedCheck_408_ = (!lean_is_exclusive(v___x_328_)) as u8;
                    if v_isSharedCheck_408_ == 0 {
                        v___x_403_ = v___x_328_;
                        v_isShared_404_ = v_isSharedCheck_408_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_401_);
                        lean_dec(v___x_328_);
                        v___x_403_ = lean_box(0);
                        v_isShared_404_ = v_isSharedCheck_408_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_346_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_currNamespace_331_, v_ns_323_);
                lean_inc(v___x_346_);
                v___x_347_ = l_Lean_Environment_registerNamespace(v_env_332_, v___x_346_);
                if v_isShared_345_ == 0 {
                    lean_ctor_set(v___x_344_, 0, v___x_347_);
                    v___x_349_ = v___x_344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_347_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 1, v_messages_333_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 2, v_scopes_334_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 3, v_usedQuotCtxts_335_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 4, v_nextMacroScope_336_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 5, v_maxRecDepth_337_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 6, v_ngen_338_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 7, v_auxDeclNGen_339_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 8, v_infoState_340_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 9, v_traceState_341_);
                    lean_ctor_set(v_reuseFailAlloc_399_, 10, v_snapshotTasks_342_);
                    v___x_349_ = v_reuseFailAlloc_399_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_350_ = lean_st_ref_set(v_a_326_, v___x_349_);
                v___f_351_ = lean_alloc_closure(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_351_, 0, v___x_346_);
                v___x_352_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_351_, v_a_326_);
                if lean_obj_tag(v___x_352_) == 0 {
                    lean_dec_ref_known(v___x_352_, 1);
                    v___f_353_ = lean_alloc_closure(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_353_, 0, v_currNamespace_331_);
                    lean_inc(v_a_326_);
                    lean_inc_ref(v_a_325_);
                    v_r_354_ = lean_apply_3(v_m_324_, v_a_325_, v_a_326_, lean_box(0));
                    if lean_obj_tag(v_r_354_) == 0 {
                        v_a_355_ = lean_ctor_get(v_r_354_, 0);
                        lean_inc(v_a_355_);
                        lean_dec_ref_known(v_r_354_, 1);
                        v___x_356_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_353_, v_a_326_);
                        if lean_obj_tag(v___x_356_) == 0 {
                            v_isSharedCheck_363_ = (!lean_is_exclusive(v___x_356_)) as u8;
                            if v_isSharedCheck_363_ == 0 {
                                v_unused_364_ = lean_ctor_get(v___x_356_, 0);
                                lean_dec(v_unused_364_);
                                v___x_358_ = v___x_356_;
                                v_isShared_359_ = v_isSharedCheck_363_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_356_);
                                v___x_358_ = lean_box(0);
                                v_isShared_359_ = v_isSharedCheck_363_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_355_);
                            v_a_365_ = lean_ctor_get(v___x_356_, 0);
                            v_isSharedCheck_372_ = (!lean_is_exclusive(v___x_356_)) as u8;
                            if v_isSharedCheck_372_ == 0 {
                                v___x_367_ = v___x_356_;
                                v_isShared_368_ = v_isSharedCheck_372_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_365_);
                                lean_dec(v___x_356_);
                                v___x_367_ = lean_box(0);
                                v_isShared_368_ = v_isSharedCheck_372_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_373_ = lean_ctor_get(v_r_354_, 0);
                        lean_inc(v_a_373_);
                        lean_dec_ref_known(v_r_354_, 1);
                        v___x_374_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_353_, v_a_326_);
                        if lean_obj_tag(v___x_374_) == 0 {
                            v_isSharedCheck_381_ = (!lean_is_exclusive(v___x_374_)) as u8;
                            if v_isSharedCheck_381_ == 0 {
                                v_unused_382_ = lean_ctor_get(v___x_374_, 0);
                                lean_dec(v_unused_382_);
                                v___x_376_ = v___x_374_;
                                v_isShared_377_ = v_isSharedCheck_381_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_374_);
                                v___x_376_ = lean_box(0);
                                v_isShared_377_ = v_isSharedCheck_381_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_373_);
                            v_a_383_ = lean_ctor_get(v___x_374_, 0);
                            v_isSharedCheck_390_ = (!lean_is_exclusive(v___x_374_)) as u8;
                            if v_isSharedCheck_390_ == 0 {
                                v___x_385_ = v___x_374_;
                                v_isShared_386_ = v_isSharedCheck_390_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_383_);
                                lean_dec(v___x_374_);
                                v___x_385_ = lean_box(0);
                                v_isShared_386_ = v_isSharedCheck_390_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_currNamespace_331_);
                    lean_dec_ref(v_m_324_);
                    v_a_391_ = lean_ctor_get(v___x_352_, 0);
                    v_isSharedCheck_398_ = (!lean_is_exclusive(v___x_352_)) as u8;
                    if v_isSharedCheck_398_ == 0 {
                        v___x_393_ = v___x_352_;
                        v_isShared_394_ = v_isSharedCheck_398_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_391_);
                        lean_dec(v___x_352_);
                        v___x_393_ = lean_box(0);
                        v_isShared_394_ = v_isSharedCheck_398_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_359_ == 0 {
                    lean_ctor_set(v___x_358_, 0, v_a_355_);
                    v___x_361_ = v___x_358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_355_);
                    v___x_361_ = v_reuseFailAlloc_362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_361_;
            }
            5 => {
                if v_isShared_368_ == 0 {
                    v___x_370_ = v___x_367_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
                    v___x_370_ = v_reuseFailAlloc_371_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_370_;
            }
            7 => {
                if v_isShared_377_ == 0 {
                    lean_ctor_set_tag(v___x_376_, 1);
                    lean_ctor_set(v___x_376_, 0, v_a_373_);
                    v___x_379_ = v___x_376_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_373_);
                    v___x_379_ = v_reuseFailAlloc_380_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_379_;
            }
            9 => {
                if v_isShared_386_ == 0 {
                    v___x_388_ = v___x_385_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
                    v___x_388_ = v_reuseFailAlloc_389_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_388_;
            }
            11 => {
                if v_isShared_394_ == 0 {
                    v___x_396_ = v___x_393_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
                    v___x_396_ = v_reuseFailAlloc_397_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_396_;
            }
            13 => {
                if v_isShared_404_ == 0 {
                    v___x_406_ = v___x_403_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
                    v___x_406_ = v_reuseFailAlloc_407_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___boxed(
    mut v_ns_409_: *mut LeanObject,
    mut v_m_410_: *mut LeanObject,
    mut v_a_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v_a_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_res_414_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v_ns_409_, v_m_410_, v_a_411_, v_a_412_);
    lean_dec(v_a_412_);
    lean_dec_ref(v_a_411_);
    return v_res_414_;
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(
    mut v_00_u03b1_415_: *mut LeanObject,
    mut v_ns_416_: *mut LeanObject,
    mut v_m_417_: *mut LeanObject,
    mut v_a_418_: *mut LeanObject,
    mut v_a_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    v___x_421_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v_ns_416_, v_m_417_, v_a_418_, v_a_419_);
    return v___x_421_;
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___boxed(
    mut v_00_u03b1_422_: *mut LeanObject,
    mut v_ns_423_: *mut LeanObject,
    mut v_m_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
    mut v_a_426_: *mut LeanObject,
    mut v_a_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_428_: *mut LeanObject = core::ptr::null_mut();
    v_res_428_ =
        l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(
            v_00_u03b1_422_,
            v_ns_423_,
            v_m_424_,
            v_a_425_,
            v_a_426_,
        );
    lean_dec(v_a_426_);
    lean_dec_ref(v_a_425_);
    return v_res_428_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    v___x_429_ = lean_box(0);
    v___x_430_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_431_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_431_, 0, v___x_430_);
    lean_ctor_set(v___x_431_, 1, v___x_429_);
    return v___x_431_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0);
    v___x_434_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_434_, 0, v___x_433_);
    return v___x_434_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___boxed(
    mut v___y_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_436_: *mut LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
    return v_res_436_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(
    mut v_00_u03b1_437_: *mut LeanObject,
    mut v___y_438_: *mut LeanObject,
    mut v___y_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
    return v___x_441_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___boxed(
    mut v_00_u03b1_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_446_: *mut LeanObject = core::ptr::null_mut();
    v_res_446_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(v_00_u03b1_442_, v___y_443_, v___y_444_);
    lean_dec(v___y_444_);
    lean_dec_ref(v___y_443_);
    return v_res_446_;
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(
    mut v_x_459_: *mut LeanObject,
    mut v_a_460_: *mut LeanObject,
    mut v_a_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: u8 = 0;
    v___x_463_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4;
    lean_inc(v_x_459_);
    v___x_464_ = l_Lean_Syntax_isOfKind(v_x_459_, v___x_463_);
    if v___x_464_ == 0 {
        let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_459_);
        v___x_465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
        return v___x_465_;
    } else {
        let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ns_467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_469_: u8 = 0;
        v___x_466_ = lean_unsigned_to_nat(1);
        v_ns_467_ = l_Lean_Syntax_getArg(v_x_459_, v___x_466_);
        v___x_468_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6;
        lean_inc(v_ns_467_);
        v___x_469_ = l_Lean_Syntax_isOfKind(v_ns_467_, v___x_468_);
        if v___x_469_ == 0 {
            let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_ns_467_);
            lean_dec(v_x_459_);
            v___x_470_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
            return v___x_470_;
        } else {
            let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
            v___x_471_ = lean_unsigned_to_nat(2);
            v___x_472_ = l_Lean_Syntax_getArg(v_x_459_, v___x_471_);
            lean_dec(v_x_459_);
            v___x_473_ = l_Lean_TSyntax_getId(v_ns_467_);
            lean_dec(v_ns_467_);
            v___x_474_ = lean_alloc_closure(
                l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                4,
                1,
            );
            lean_closure_set(v___x_474_, 0, v___x_472_);
            v___x_475_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v___x_473_, v___x_474_, v_a_460_, v_a_461_);
            return v___x_475_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed(
    mut v_x_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
    mut v_a_478_: *mut LeanObject,
    mut v_a_479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_480_: *mut LeanObject = core::ptr::null_mut();
    v_res_480_ =
        l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(
            v_x_476_, v_a_477_, v_a_478_,
        );
    lean_dec(v_a_478_);
    lean_dec_ref(v_a_477_);
    return v_res_480_;
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1()
-> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_517_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4;
    v___x_518_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13;
    v___x_519_ = lean_alloc_closure(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_520_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_516_, v___x_517_, v___x_518_, v___x_519_,
    );
    return v___x_520_;
}
pub unsafe fn l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___boxed(
    mut v_a_521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_522_: *mut LeanObject = core::ptr::null_mut();
    v_res_522_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1();
    return v_res_522_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Command_WithWeakNamespace(
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
    res = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Command_WithWeakNamespace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Command_WithWeakNamespace(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
}
