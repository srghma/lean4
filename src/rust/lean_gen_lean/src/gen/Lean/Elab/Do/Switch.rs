// Lean compiler output
// Module: Lean.Elab.Do.Switch
// Imports: Lean.Elab.Term.TermElabM Lean.Elab.Do.Basic Lean.Elab.Do.Legacy
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_setKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_elabDo, l_Lean_Elab_Do_elabNestedAction___redArg,
    runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Do::Legacy::{
    initialize_Lean_Elab_Do_Legacy, l_Lean_Elab_Term_Do_elabDo,
    l_Lean_Elab_Term_elabNestedAction___redArg, runtime_initialize_Lean_Elab_Do_Legacy,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    initialize_Lean_Elab_Term_TermElabM, l_Lean_Elab_Term_termElabAttribute,
    runtime_initialize_Lean_Elab_Term_TermElabM,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 101, 103, 97, 99, 121, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15861075605163525197 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9742257359965486643 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5528038093041166455 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [85, 115, 101, 32, 116, 104, 101, 32, 108, 101, 103, 97, 99, 121, 32, 96, 100, 111, 96, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 116, 104, 101, 32, 110, 101, 119, 44, 32, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17933644290606856182 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8440447815677265228 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,18303184360037518452 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Term_backward_do_legacy: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5817315006727311029 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0],
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        3326968124746134365 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0],
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        940684074193935882 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_expandTermFor___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 111, 70, 111, 114, 0],
    };
static mut l_Lean_Elab_Term_expandTermFor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermFor___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_expandTermFor___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermFor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16953626593407929508 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandTermFor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermFor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value) as *mut crate::leanh::LeanObject,17779544069271969889 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 112, 97, 110, 100, 84, 101, 114, 109, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value) as *mut crate::leanh::LeanObject,14473145420124210151 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1805 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1805 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 57 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 57 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1805 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1805 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandTermTry___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Term_expandTermTry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermTry___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_expandTermTry___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermTry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14629134714403383735 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandTermTry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermTry___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 84, 114, 121, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value) as *mut crate::leanh::LeanObject,6401473892203253886 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 112, 97, 110, 100, 84, 101, 114, 109, 84, 114, 121, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value) as *mut crate::leanh::LeanObject,6095822636559982209 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1808 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1808 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 57 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 57 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1808 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1808 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandTermUnless___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [100, 111, 85, 110, 108, 101, 115, 115, 0],
    };
static mut l_Lean_Elab_Term_expandTermUnless___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermUnless___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_expandTermUnless___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermUnless___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17291926084577229031 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandTermUnless___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermUnless___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 85, 110, 108, 101, 115, 115, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value) as *mut crate::leanh::LeanObject,16804342611006610865 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 120, 112, 97, 110, 100, 84, 101, 114, 109, 85, 110, 108, 101, 115, 115, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value) as *mut crate::leanh::LeanObject,12390237352576341826 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1811 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1811 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1811 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1811 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandTermReturn___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [100, 111, 82, 101, 116, 117, 114, 110, 0],
    };
static mut l_Lean_Elab_Term_expandTermReturn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermReturn___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_expandTermReturn___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandTermReturn___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2825454143963843026 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandTermReturn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandTermReturn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 82, 101, 116, 117, 114, 110, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value) as *mut crate::leanh::LeanObject,3520575480207570375 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 120, 112, 97, 110, 100, 84, 101, 114, 109, 82, 101, 116, 117, 114, 110, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value) as *mut crate::leanh::LeanObject,12812407647857056090 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1814 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1814 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1814 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1814 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 108, 97, 98, 68, 111, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value) as *mut crate::leanh::LeanObject,12384803775341245224 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 101, 115, 116, 101, 100, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0_value) as *mut crate::leanh::LeanObject,14598754423419706227 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 108, 97, 98, 84, 101, 114, 109, 78, 101, 115, 116, 101, 100, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2_value) as *mut crate::leanh::LeanObject,8094577510062019594 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(
    mut v_name_491_: *mut crate::leanh::LeanObject,
    mut v_decl_492_: *mut crate::leanh::LeanObject,
    mut v_ref_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: u8 = 0;
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_509_: u8 = 0;
    let mut v_unused_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_514_: u8 = 0;
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_495_ = crate::leanh::lean_ctor_get(v_decl_492_, 0);
                v_descr_496_ = crate::leanh::lean_ctor_get(v_decl_492_, 1);
                v_deprecation_x3f_497_ = crate::leanh::lean_ctor_get(v_decl_492_, 2);
                v___x_498_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_499_ = (crate::leanh::lean_unbox(v_defValue_495_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_498_, 0 as u32, v___x_499_);
                crate::leanh::lean_inc(v_deprecation_x3f_497_);
                crate::leanh::lean_inc_ref(v_descr_496_);
                crate::leanh::lean_inc_n(v_name_491_, 2);
                v___x_500_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_500_, 0, v_name_491_);
                crate::leanh::lean_ctor_set(v___x_500_, 1, v_ref_493_);
                crate::leanh::lean_ctor_set(v___x_500_, 2, v___x_498_);
                crate::leanh::lean_ctor_set(v___x_500_, 3, v_descr_496_);
                crate::leanh::lean_ctor_set(v___x_500_, 4, v_deprecation_x3f_497_);
                v___x_501_ = lean_register_option(v_name_491_, v___x_500_);
                if crate::leanh::lean_obj_tag(v___x_501_) == 0 {
                    v_isSharedCheck_509_ = (!crate::leanh::lean_is_exclusive(v___x_501_)) as u8;
                    if v_isSharedCheck_509_ == 0 {
                        v_unused_510_ = crate::leanh::lean_ctor_get(v___x_501_, 0);
                        crate::leanh::lean_dec(v_unused_510_);
                        v___x_503_ = v___x_501_;
                        v_isShared_504_ = v_isSharedCheck_509_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_501_);
                        v___x_503_ = crate::leanh::lean_box(0);
                        v_isShared_504_ = v_isSharedCheck_509_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_491_);
                    v_a_511_ = crate::leanh::lean_ctor_get(v___x_501_, 0);
                    v_isSharedCheck_518_ = (!crate::leanh::lean_is_exclusive(v___x_501_)) as u8;
                    if v_isSharedCheck_518_ == 0 {
                        v___x_513_ = v___x_501_;
                        v_isShared_514_ = v_isSharedCheck_518_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_511_);
                        crate::leanh::lean_dec(v___x_501_);
                        v___x_513_ = crate::leanh::lean_box(0);
                        v_isShared_514_ = v_isSharedCheck_518_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_495_);
                v___x_505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_505_, 0, v_name_491_);
                crate::leanh::lean_ctor_set(v___x_505_, 1, v_defValue_495_);
                if v_isShared_504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_505_);
                    v___x_507_ = v___x_503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
                    v___x_507_ = v_reuseFailAlloc_508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_507_;
            }
            3 => {
                if v_isShared_514_ == 0 {
                    v___x_516_ = v___x_513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
                    v___x_516_ = v_reuseFailAlloc_517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_519_: *mut crate::leanh::LeanObject,
    mut v_decl_520_: *mut crate::leanh::LeanObject,
    mut v_ref_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_523_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(v_name_519_, v_decl_520_, v_ref_521_);
    crate::leanh::lean_dec_ref(v_decl_520_);
    return v_res_523_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_548_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_;
    v___x_549_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_;
    v___x_550_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_;
    v___x_551_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(v___x_548_, v___x_549_, v___x_550_);
    return v___x_551_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4____boxed(
    mut v_a_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_();
    return v_res_553_;
}
pub unsafe fn _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_575_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_575_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(
    mut v_newKind_576_: *mut crate::leanh::LeanObject,
    mut v_stx_577_: *mut crate::leanh::LeanObject,
    mut v_a_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_580_ = crate::leanh::lean_ctor_get(v_a_578_, 5);
    v_stx_581_ = l_Lean_Syntax_setKind(v_stx_577_, v_newKind_576_);
    v_ref_582_ = l_Lean_replaceRef(v_stx_581_, v_ref_580_);
    v___x_583_ = 0;
    v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_582_, v___x_583_);
    crate::leanh::lean_dec(v_ref_582_);
    v___x_585_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_;
    v___x_586_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1;
    crate::leanh::lean_inc_n(v___x_584_, 5);
    v___x_587_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_587_, 0, v___x_584_);
    crate::leanh::lean_ctor_set(v___x_587_, 1, v___x_585_);
    v___x_588_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3;
    v___x_589_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5;
    v___x_590_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7;
    v___x_591_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once
        ),
        _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8,
    );
    v___x_592_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_584_);
    crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_589_);
    crate::leanh::lean_ctor_set(v___x_592_, 2, v___x_591_);
    v___x_593_ = l_Lean_Syntax_node2(v___x_584_, v___x_590_, v_stx_581_, v___x_592_);
    v___x_594_ = l_Lean_Syntax_node1(v___x_584_, v___x_589_, v___x_593_);
    v___x_595_ = l_Lean_Syntax_node1(v___x_584_, v___x_588_, v___x_594_);
    v___x_596_ = l_Lean_Syntax_node2(v___x_584_, v___x_586_, v___x_587_, v___x_595_);
    v___x_597_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_597_, 0, v___x_596_);
    crate::leanh::lean_ctor_set(v___x_597_, 1, v_a_579_);
    return v___x_597_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(
    mut v_newKind_598_: *mut crate::leanh::LeanObject,
    mut v_stx_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
    mut v_a_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_602_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(
        v_newKind_598_,
        v_stx_599_,
        v_a_600_,
        v_a_601_,
    );
    crate::leanh::lean_dec_ref(v_a_600_);
    return v_res_602_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermFor(
    mut v_a_609_: *mut crate::leanh::LeanObject,
    mut v_a_610_: *mut crate::leanh::LeanObject,
    mut v_a_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = l_Lean_Elab_Term_expandTermFor___closed__1;
    v___x_613_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(
        v___x_612_, v_a_609_, v_a_610_, v_a_611_,
    );
    return v___x_613_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermFor___boxed(
    mut v_a_614_: *mut crate::leanh::LeanObject,
    mut v_a_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Lean_Elab_Term_expandTermFor(v_a_614_, v_a_615_, v_a_616_);
    crate::leanh::lean_dec_ref(v_a_615_);
    return v_res_617_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Elab_macroAttribute;
    v___x_632_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1;
    v___x_633_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3;
    v___x_634_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_expandTermFor___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_635_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_631_, v___x_632_, v___x_633_, v___x_634_,
    );
    return v___x_635_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___boxed(
    mut v_a_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
    return v_res_637_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3;
    v___x_665_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6;
    v___x_666_ = l_Lean_addBuiltinDeclarationRanges(v___x_664_, v___x_665_);
    return v___x_666_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___boxed(
    mut v_a_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_668_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
    return v_res_668_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermTry(
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_a_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Lean_Elab_Term_expandTermTry___closed__1;
    v___x_679_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(
        v___x_678_, v_a_675_, v_a_676_, v_a_677_,
    );
    return v___x_679_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermTry___boxed(
    mut v_a_680_: *mut crate::leanh::LeanObject,
    mut v_a_681_: *mut crate::leanh::LeanObject,
    mut v_a_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lean_Elab_Term_expandTermTry(v_a_680_, v_a_681_, v_a_682_);
    crate::leanh::lean_dec_ref(v_a_681_);
    return v_res_683_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lean_Elab_macroAttribute;
    v___x_698_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1;
    v___x_699_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3;
    v___x_700_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_expandTermTry___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_697_, v___x_698_, v___x_699_, v___x_700_,
    );
    return v___x_701_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___boxed(
    mut v_a_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
    return v_res_703_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_730_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3;
    v___x_731_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6;
    v___x_732_ = l_Lean_addBuiltinDeclarationRanges(v___x_730_, v___x_731_);
    return v___x_732_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___boxed(
    mut v_a_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
    return v_res_734_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermUnless(
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Lean_Elab_Term_expandTermUnless___closed__1;
    v___x_745_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(
        v___x_744_, v_a_741_, v_a_742_, v_a_743_,
    );
    return v___x_745_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermUnless___boxed(
    mut v_a_746_: *mut crate::leanh::LeanObject,
    mut v_a_747_: *mut crate::leanh::LeanObject,
    mut v_a_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Lean_Elab_Term_expandTermUnless(v_a_746_, v_a_747_, v_a_748_);
    crate::leanh::lean_dec_ref(v_a_747_);
    return v_res_749_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_763_ = l_Lean_Elab_macroAttribute;
    v___x_764_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1;
    v___x_765_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3;
    v___x_766_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_expandTermUnless___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_767_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_763_, v___x_764_, v___x_765_, v___x_766_,
    );
    return v___x_767_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___boxed(
    mut v_a_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_769_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
    return v_res_769_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3;
    v___x_797_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6;
    v___x_798_ = l_Lean_addBuiltinDeclarationRanges(v___x_796_, v___x_797_);
    return v___x_798_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___boxed(
    mut v_a_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_800_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
    return v_res_800_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermReturn(
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Lean_Elab_Term_expandTermReturn___closed__1;
    v___x_811_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(
        v___x_810_, v_a_807_, v_a_808_, v_a_809_,
    );
    return v___x_811_;
}
pub unsafe fn l_Lean_Elab_Term_expandTermReturn___boxed(
    mut v_a_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_a_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_815_ = l_Lean_Elab_Term_expandTermReturn(v_a_812_, v_a_813_, v_a_814_);
    crate::leanh::lean_dec_ref(v_a_813_);
    return v_res_815_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = l_Lean_Elab_macroAttribute;
    v___x_830_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1;
    v___x_831_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3;
    v___x_832_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_expandTermReturn___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_833_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_829_, v___x_830_, v___x_831_, v___x_832_,
    );
    return v___x_833_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___boxed(
    mut v_a_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
    return v_res_835_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3;
    v___x_863_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6;
    v___x_864_ = l_Lean_addBuiltinDeclarationRanges(v___x_862_, v___x_863_);
    return v___x_864_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___boxed(
    mut v_a_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_866_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
    return v_res_866_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(
    mut v_opts_867_: *mut crate::leanh::LeanObject,
    mut v_opt_868_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_869_ = crate::leanh::lean_ctor_get(v_opt_868_, 0);
    v_defValue_870_ = crate::leanh::lean_ctor_get(v_opt_868_, 1);
    v_map_871_ = crate::leanh::lean_ctor_get(v_opts_867_, 0);
    v___x_872_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_871_,
            v_name_869_,
        );
    if crate::leanh::lean_obj_tag(v___x_872_) == 0 {
        let mut v___x_873_: u8 = 0;
        v___x_873_ = (crate::leanh::lean_unbox(v_defValue_870_) as u8);
        return v___x_873_;
    } else {
        let mut v_val_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_874_ = crate::leanh::lean_ctor_get(v___x_872_, 0);
        crate::leanh::lean_inc(v_val_874_);
        crate::leanh::lean_dec_ref_known(v___x_872_, 1);
        if crate::leanh::lean_obj_tag(v_val_874_) == 1 {
            let mut v_v_875_: u8 = 0;
            v_v_875_ = crate::leanh::lean_ctor_get_uint8(v_val_874_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_874_, 0);
            return v_v_875_;
        } else {
            let mut v___x_876_: u8 = 0;
            crate::leanh::lean_dec(v_val_874_);
            v___x_876_ = (crate::leanh::lean_unbox(v_defValue_870_) as u8);
            return v___x_876_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0___boxed(
    mut v_opts_877_: *mut crate::leanh::LeanObject,
    mut v_opt_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_879_: u8 = 0;
    let mut v_r_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_opts_877_, v_opt_878_);
    crate::leanh::lean_dec_ref(v_opt_878_);
    crate::leanh::lean_dec_ref(v_opts_877_);
    v_r_880_ = crate::leanh::lean_box((v_res_879_) as usize);
    return v_r_880_;
}
pub unsafe fn l_Lean_Elab_Term_elabDo(
    mut v_stx_881_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_882_: *mut crate::leanh::LeanObject,
    mut v_a_883_: *mut crate::leanh::LeanObject,
    mut v_a_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: u8 = 0;
    v_options_890_ = crate::leanh::lean_ctor_get(v_a_887_, 2);
    v___x_891_ = l_Lean_Elab_Term_backward_do_legacy;
    v___x_892_ =
        l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_options_890_, v___x_891_);
    if v___x_892_ == 0 {
        let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_893_ = l_Lean_Elab_Do_elabDo(
            v_stx_881_,
            v_expectedType_x3f_882_,
            v_a_883_,
            v_a_884_,
            v_a_885_,
            v_a_886_,
            v_a_887_,
            v_a_888_,
        );
        return v___x_893_;
    } else {
        let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_894_ = l_Lean_Elab_Term_Do_elabDo(
            v_stx_881_,
            v_expectedType_x3f_882_,
            v_a_883_,
            v_a_884_,
            v_a_885_,
            v_a_886_,
            v_a_887_,
            v_a_888_,
        );
        return v___x_894_;
    }
}
pub unsafe fn l_Lean_Elab_Term_elabDo___boxed(
    mut v_stx_895_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_896_: *mut crate::leanh::LeanObject,
    mut v_a_897_: *mut crate::leanh::LeanObject,
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
    mut v_a_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l_Lean_Elab_Term_elabDo(
        v_stx_895_,
        v_expectedType_x3f_896_,
        v_a_897_,
        v_a_898_,
        v_a_899_,
        v_a_900_,
        v_a_901_,
        v_a_902_,
    );
    crate::leanh::lean_dec(v_a_902_);
    crate::leanh::lean_dec_ref(v_a_901_);
    crate::leanh::lean_dec(v_a_900_);
    crate::leanh::lean_dec_ref(v_a_899_);
    crate::leanh::lean_dec(v_a_898_);
    crate::leanh::lean_dec_ref(v_a_897_);
    return v_res_904_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_913_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1;
    v___x_914_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1;
    v___x_915_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_elabDo___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_916_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_912_, v___x_913_, v___x_914_, v___x_915_,
    );
    return v___x_916_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(
    mut v_a_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
    return v_res_918_;
}
pub unsafe fn l_Lean_Elab_Term_elabTermNestedAction___redArg(
    mut v_stx_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
    mut v_a_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
    mut v_a_924_: *mut crate::leanh::LeanObject,
    mut v_a_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    v_options_927_ = crate::leanh::lean_ctor_get(v_a_924_, 2);
    v___x_928_ = l_Lean_Elab_Term_backward_do_legacy;
    v___x_929_ =
        l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_options_927_, v___x_928_);
    if v___x_929_ == 0 {
        let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_930_ = l_Lean_Elab_Do_elabNestedAction___redArg(
            v_stx_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_,
        );
        return v___x_930_;
    } else {
        let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_931_ = l_Lean_Elab_Term_elabNestedAction___redArg(
            v_stx_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_,
        );
        crate::leanh::lean_dec(v_stx_919_);
        return v___x_931_;
    }
}
pub unsafe fn l_Lean_Elab_Term_elabTermNestedAction___redArg___boxed(
    mut v_stx_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
    mut v_a_938_: *mut crate::leanh::LeanObject,
    mut v_a_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_940_ = l_Lean_Elab_Term_elabTermNestedAction___redArg(
        v_stx_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_,
    );
    crate::leanh::lean_dec(v_a_938_);
    crate::leanh::lean_dec_ref(v_a_937_);
    crate::leanh::lean_dec(v_a_936_);
    crate::leanh::lean_dec_ref(v_a_935_);
    crate::leanh::lean_dec(v_a_934_);
    crate::leanh::lean_dec_ref(v_a_933_);
    return v_res_940_;
}
pub unsafe fn l_Lean_Elab_Term_elabTermNestedAction(
    mut v_stx_941_: *mut crate::leanh::LeanObject,
    mut v_ty_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_950_ = l_Lean_Elab_Term_elabTermNestedAction___redArg(
        v_stx_941_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_,
    );
    return v___x_950_;
}
pub unsafe fn l_Lean_Elab_Term_elabTermNestedAction___boxed(
    mut v_stx_951_: *mut crate::leanh::LeanObject,
    mut v_ty_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
    mut v_a_957_: *mut crate::leanh::LeanObject,
    mut v_a_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Lean_Elab_Term_elabTermNestedAction(
        v_stx_951_, v_ty_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_,
    );
    crate::leanh::lean_dec(v_a_958_);
    crate::leanh::lean_dec_ref(v_a_957_);
    crate::leanh::lean_dec(v_a_956_);
    crate::leanh::lean_dec_ref(v_a_955_);
    crate::leanh::lean_dec(v_a_954_);
    crate::leanh::lean_dec_ref(v_a_953_);
    crate::leanh::lean_dec(v_ty_952_);
    return v_res_960_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_975_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1;
    v___x_976_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3;
    v___x_977_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_elabTermNestedAction___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_978_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_974_, v___x_975_, v___x_976_, v___x_977_,
    );
    return v___x_978_;
}
pub unsafe fn l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___boxed(
    mut v_a_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1();
    return v_res_980_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Do_Switch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Legacy(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Term_backward_do_legacy = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Term_backward_do_legacy);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Do_Switch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Do_Switch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Do_Legacy(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Switch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Do_Switch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Do_Switch(builtin);
}
