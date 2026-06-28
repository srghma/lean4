// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Normalize
// Imports: Lean.Meta.Tactic.BVDecide.Normalize
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize,
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__3_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 118, 78, 111, 114, 109, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__3_value) as *mut LeanObject,9992359010160305136 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__5_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__3_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__6_value) as *mut LeanObject,12939946447940265992 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [78, 111, 114, 109, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__8_value) as *mut LeanObject,5020615090297298225 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,353000241334249332 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__0_value) as *mut LeanObject,16574890817103426677 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__3_value) as *mut LeanObject,3374353936257450403 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__2_value) as *mut LeanObject,16037205153617603602 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__6_value) as *mut LeanObject,13748188002829770731 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__8_value) as *mut LeanObject,13391270943718779622 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__16_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 66, 86, 78, 111, 114, 109, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__16_value) as *mut LeanObject,10099294955605717016 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__17_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ = lean_box(0);
    v___x_169_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_170_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_170_, 0, v___x_169_);
    lean_ctor_set(v___x_170_, 1, v___x_168_);
    return v___x_170_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    v___x_172_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___closed__0);
    v___x_173_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_173_, 0, v___x_172_);
    return v___x_173_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg___boxed(
    mut v___y_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_175_: *mut LeanObject = core::ptr::null_mut();
    v_res_175_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg();
    return v_res_175_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v___y_177_: *mut LeanObject,
    mut v___y_178_: *mut LeanObject,
    mut v___y_179_: *mut LeanObject,
    mut v___y_180_: *mut LeanObject,
    mut v___y_181_: *mut LeanObject,
    mut v___y_182_: *mut LeanObject,
    mut v___y_183_: *mut LeanObject,
    mut v___y_184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    v___x_186_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg();
    return v___x_186_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___boxed(
    mut v_00_u03b1_187_: *mut LeanObject,
    mut v___y_188_: *mut LeanObject,
    mut v___y_189_: *mut LeanObject,
    mut v___y_190_: *mut LeanObject,
    mut v___y_191_: *mut LeanObject,
    mut v___y_192_: *mut LeanObject,
    mut v___y_193_: *mut LeanObject,
    mut v___y_194_: *mut LeanObject,
    mut v___y_195_: *mut LeanObject,
    mut v___y_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_197_: *mut LeanObject = core::ptr::null_mut();
    v_res_197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0(v_00_u03b1_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
    lean_dec(v___y_195_);
    lean_dec_ref(v___y_194_);
    lean_dec(v___y_193_);
    lean_dec_ref(v___y_192_);
    lean_dec(v___y_191_);
    lean_dec_ref(v___y_190_);
    lean_dec(v___y_189_);
    lean_dec_ref(v___y_188_);
    return v_res_197_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize(
    mut v_x_213_: *mut LeanObject,
    mut v_a_214_: *mut LeanObject,
    mut v_a_215_: *mut LeanObject,
    mut v_a_216_: *mut LeanObject,
    mut v_a_217_: *mut LeanObject,
    mut v_a_218_: *mut LeanObject,
    mut v_a_219_: *mut LeanObject,
    mut v_a_220_: *mut LeanObject,
    mut v_a_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: u8 = 0;
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: u8 = 0;
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: u8 = 0;
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_251_: u8 = 0;
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_255_: u8 = 0;
    let mut v_a_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_259_: u8 = 0;
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut v_a_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_267_: u8 = 0;
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_223_ = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4;
                lean_inc(v_x_213_);
                v___x_224_ = l_Lean_Syntax_isOfKind(v_x_213_, v___x_223_);
                if v___x_224_ == 0 {
                    lean_dec(v_x_213_);
                    v___x_225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg();
                    return v___x_225_;
                } else {
                    v___x_226_ = lean_unsigned_to_nat(1);
                    v___x_227_ = l_Lean_Syntax_getArg(v_x_213_, v___x_226_);
                    lean_dec(v_x_213_);
                    v___x_228_ = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__6;
                    lean_inc(v___x_227_);
                    v___x_229_ = l_Lean_Syntax_isOfKind(v___x_227_, v___x_228_);
                    if v___x_229_ == 0 {
                        lean_dec(v___x_227_);
                        v___x_230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize_spec__0___redArg();
                        return v___x_230_;
                    } else {
                        v___x_231_ = lean_unsigned_to_nat(10);
                        v___x_232_ = 0;
                        v___x_233_ = lean_unsigned_to_nat(100000);
                        v___x_234_ = 0;
                        v___x_235_ = lean_alloc_ctor(0, 2, (11) as u32);
                        lean_ctor_set(v___x_235_, 0, v___x_231_);
                        lean_ctor_set(v___x_235_, 1, v___x_233_);
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                            v___x_232_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 3) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 4) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 5) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 6) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 7) as u32,
                            v___x_229_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 8) as u32,
                            v___x_232_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 9) as u32,
                            v___x_232_,
                        );
                        lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 10) as u32,
                            v___x_234_,
                        );
                        v___x_236_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(
                            v___x_227_, v___x_235_, v___x_229_, v_a_214_, v_a_220_, v_a_221_,
                        );
                        if lean_obj_tag(v___x_236_) == 0 {
                            v_a_237_ = lean_ctor_get(v___x_236_, 0);
                            lean_inc(v_a_237_);
                            lean_dec_ref_known(v___x_236_, 1);
                            v___x_238_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v_a_215_, v_a_218_, v_a_219_, v_a_220_, v_a_221_,
                            );
                            if lean_obj_tag(v___x_238_) == 0 {
                                v_a_239_ = lean_ctor_get(v___x_238_, 0);
                                lean_inc(v_a_239_);
                                lean_dec_ref_known(v___x_238_, 1);
                                v___x_240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
                                    v_a_239_, v_a_237_, v_a_218_, v_a_219_, v_a_220_, v_a_221_,
                                );
                                lean_dec(v_a_237_);
                                if lean_obj_tag(v___x_240_) == 0 {
                                    v_a_241_ = lean_ctor_get(v___x_240_, 0);
                                    lean_inc(v_a_241_);
                                    lean_dec_ref_known(v___x_240_, 1);
                                    if lean_obj_tag(v_a_241_) == 0 {
                                        v___x_242_ = lean_box(0);
                                        v___x_243_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                            v___x_242_, v_a_215_, v_a_218_, v_a_219_, v_a_220_,
                                            v_a_221_,
                                        );
                                        return v___x_243_;
                                    } else {
                                        v_val_244_ = lean_ctor_get(v_a_241_, 0);
                                        lean_inc(v_val_244_);
                                        lean_dec_ref_known(v_a_241_, 1);
                                        v___x_245_ = lean_box(0);
                                        v___x_246_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_246_, 0, v_val_244_);
                                        lean_ctor_set(v___x_246_, 1, v___x_245_);
                                        v___x_247_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                            v___x_246_, v_a_215_, v_a_218_, v_a_219_, v_a_220_,
                                            v_a_221_,
                                        );
                                        return v___x_247_;
                                    }
                                } else {
                                    v_a_248_ = lean_ctor_get(v___x_240_, 0);
                                    v_isSharedCheck_255_ = (!lean_is_exclusive(v___x_240_)) as u8;
                                    if v_isSharedCheck_255_ == 0 {
                                        v___x_250_ = v___x_240_;
                                        v_isShared_251_ = v_isSharedCheck_255_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_248_);
                                        lean_dec(v___x_240_);
                                        v___x_250_ = lean_box(0);
                                        v_isShared_251_ = v_isSharedCheck_255_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_237_);
                                v_a_256_ = lean_ctor_get(v___x_238_, 0);
                                v_isSharedCheck_263_ = (!lean_is_exclusive(v___x_238_)) as u8;
                                if v_isSharedCheck_263_ == 0 {
                                    v___x_258_ = v___x_238_;
                                    v_isShared_259_ = v_isSharedCheck_263_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_256_);
                                    lean_dec(v___x_238_);
                                    v___x_258_ = lean_box(0);
                                    v_isShared_259_ = v_isSharedCheck_263_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_264_ = lean_ctor_get(v___x_236_, 0);
                            v_isSharedCheck_271_ = (!lean_is_exclusive(v___x_236_)) as u8;
                            if v_isSharedCheck_271_ == 0 {
                                v___x_266_ = v___x_236_;
                                v_isShared_267_ = v_isSharedCheck_271_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_264_);
                                lean_dec(v___x_236_);
                                v___x_266_ = lean_box(0);
                                v_isShared_267_ = v_isSharedCheck_271_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_251_ == 0 {
                    v___x_253_ = v___x_250_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
                    v___x_253_ = v_reuseFailAlloc_254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_253_;
            }
            3 => {
                if v_isShared_259_ == 0 {
                    v___x_261_ = v___x_258_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
                    v___x_261_ = v_reuseFailAlloc_262_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_261_;
            }
            5 => {
                if v_isShared_267_ == 0 {
                    v___x_269_ = v___x_266_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
                    v___x_269_ = v_reuseFailAlloc_270_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___boxed(
    mut v_x_272_: *mut LeanObject,
    mut v_a_273_: *mut LeanObject,
    mut v_a_274_: *mut LeanObject,
    mut v_a_275_: *mut LeanObject,
    mut v_a_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
    mut v_a_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_282_: *mut LeanObject = core::ptr::null_mut();
    v_res_282_ = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize(v_x_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
    lean_dec(v_a_280_);
    lean_dec_ref(v_a_279_);
    lean_dec(v_a_278_);
    lean_dec_ref(v_a_277_);
    lean_dec(v_a_276_);
    lean_dec_ref(v_a_275_);
    lean_dec(v_a_274_);
    lean_dec_ref(v_a_273_);
    return v_res_282_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1()
-> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_329_ = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___closed__4;
    v___x_330_ = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___closed__17;
    v___x_331_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_332_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_328_, v___x_329_, v___x_330_, v___x_331_,
    );
    return v___x_332_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1___boxed(
    mut v_a_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1();
    return v_res_334_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_BVDecide_Normalize_0__Lean_Elab_Tactic_BVDecide_Normalize_evalBVNormalize__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin);
}
