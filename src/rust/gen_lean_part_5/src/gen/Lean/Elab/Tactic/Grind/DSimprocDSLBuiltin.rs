// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.DSimprocDSLBuiltin
// Imports: Lean.Elab.Tactic.Grind.DSimprocDSL Init.Sym.DSimp.DSimprocDSL Lean.Meta.Sym.DSimp.Reduce Lean.Meta.Sym.DSimp.DSimproc
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Init::Sym::DSimp::DSimprocDSL::{
    initialize_Init_Sym_DSimp_DSimprocDSL, runtime_initialize_Init_Sym_DSimp_DSimprocDSL,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Grind::DSimprocDSL::{
    initialize_Lean_Elab_Tactic_Grind_DSimprocDSL, l_Lean_Elab_Tactic_Grind_elabSymDSimproc,
    l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute,
    runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimproc::{
    initialize_Lean_Meta_Sym_DSimp_DSimproc, runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::Reduce::{
    initialize_Lean_Meta_Sym_DSimp_Reduce, l_Lean_Meta_Sym_DSimp_beta___boxed,
    l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed, l_Lean_Meta_Sym_DSimp_dsimpProj___boxed,
    l_Lean_Meta_Sym_DSimp_zeta___boxed, l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed,
    runtime_initialize_Lean_Meta_Sym_DSimp_Reduce,
};
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__4_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [122, 101, 116, 97, 68, 101, 108, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__4_value) as *mut leanh::LeanObject,2119463912076888173 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__6_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__9_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__11_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__11_value) as *mut leanh::LeanObject,5409699204079762053 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__13_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__13_value) as *mut leanh::LeanObject,4907018543776028915 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__15_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [68, 83, 105, 109, 112, 114, 111, 99, 68, 83, 76, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__14_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__15_value) as *mut leanh::LeanObject,1206720768524454486 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__16_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1920802545335962495 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__17_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,2640933283368869554 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__18_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__9_value) as *mut leanh::LeanObject,4910598027162449360 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__19_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__11_value) as *mut leanh::LeanObject,10903878732957412653 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__20_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__13_value) as *mut leanh::LeanObject,17250401432640087163 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__22_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 108, 97, 98, 90, 101, 116, 97, 68, 101, 108, 116, 97, 65, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__22_value) as *mut leanh::LeanObject,9769496823605989636 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_DSimp_zeta___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__0_value) as *mut leanh::LeanObject,16596319664338446668 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 90, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__2_value) as *mut leanh::LeanObject,6615529073448461677 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_DSimp_beta___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__0_value) as *mut leanh::LeanObject,154037570533536172 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 66, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__2_value) as *mut leanh::LeanObject,11389442473113813946 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 101, 100, 117, 99, 101, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__0_value) as *mut leanh::LeanObject,14884666146178512216 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__2_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 82, 101, 100, 117, 99, 101, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__2_value) as *mut leanh::LeanObject,11103498670029342025 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_DSimp_dsimpProj___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__0_value) as *mut leanh::LeanObject,15045140164005891883 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__2_value) as *mut leanh::LeanObject,13715001865984117434 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__0_value) as *mut leanh::LeanObject,10522018292007760565 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__2_value) as *mut leanh::LeanObject,3379642001659079152 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 84, 104, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__0_value) as *mut leanh::LeanObject,15118032029328637794 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 68, 83, 105, 109, 112, 114, 111, 99, 65, 110, 100, 84, 104, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__0_value) as *mut leanh::LeanObject,16391997820585047688 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__0_value) as *mut leanh::LeanObject,12448059518168016466 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 68, 83, 105, 109, 112, 114, 111, 99, 79, 114, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__0_value) as *mut leanh::LeanObject,13068631587827567331 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 115, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__3_value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__0_value) as *mut leanh::LeanObject,12358822129129543384 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 68, 83, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__0_value) as *mut leanh::LeanObject,1389155367457317387 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg___closed__0;
    v___x_631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_631_, 0, v___x_630_);
    return v___x_631_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg___boxed(
    mut v_a_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_633_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg();
    return v_res_633_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll(
    mut v_x_634_: *mut leanh::LeanObject,
    mut v_a_635_: *mut leanh::LeanObject,
    mut v_a_636_: *mut leanh::LeanObject,
    mut v_a_637_: *mut leanh::LeanObject,
    mut v_a_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
    mut v_a_640_: *mut leanh::LeanObject,
    mut v_a_641_: *mut leanh::LeanObject,
    mut v_a_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___redArg();
    return v___x_644_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___boxed(
    mut v_x_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
    mut v_a_649_: *mut leanh::LeanObject,
    mut v_a_650_: *mut leanh::LeanObject,
    mut v_a_651_: *mut leanh::LeanObject,
    mut v_a_652_: *mut leanh::LeanObject,
    mut v_a_653_: *mut leanh::LeanObject,
    mut v_a_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_655_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll(v_x_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
    leanh::lean_dec(v_a_653_);
    leanh::lean_dec_ref(v_a_652_);
    leanh::lean_dec(v_a_651_);
    leanh::lean_dec_ref(v_a_650_);
    leanh::lean_dec(v_a_649_);
    leanh::lean_dec_ref(v_a_648_);
    leanh::lean_dec(v_a_647_);
    leanh::lean_dec_ref(v_a_646_);
    leanh::lean_dec(v_x_645_);
    return v_res_655_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1()
-> *mut leanh::LeanObject {
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_711_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__5;
    v___x_712_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___closed__23;
    v___x_713_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_714_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_710_, v___x_711_, v___x_712_, v___x_713_,
    );
    return v___x_714_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1___boxed(
    mut v_a_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1();
    return v_res_716_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg___closed__0;
    v___x_720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_720_, 0, v___x_719_);
    return v___x_720_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg___boxed(
    mut v_a_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_722_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg();
    return v_res_722_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta(
    mut v_x_723_: *mut leanh::LeanObject,
    mut v_a_724_: *mut leanh::LeanObject,
    mut v_a_725_: *mut leanh::LeanObject,
    mut v_a_726_: *mut leanh::LeanObject,
    mut v_a_727_: *mut leanh::LeanObject,
    mut v_a_728_: *mut leanh::LeanObject,
    mut v_a_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___redArg();
    return v___x_733_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___boxed(
    mut v_x_734_: *mut leanh::LeanObject,
    mut v_a_735_: *mut leanh::LeanObject,
    mut v_a_736_: *mut leanh::LeanObject,
    mut v_a_737_: *mut leanh::LeanObject,
    mut v_a_738_: *mut leanh::LeanObject,
    mut v_a_739_: *mut leanh::LeanObject,
    mut v_a_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_a_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ =
        l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta(
            v_x_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_,
            v_a_742_,
        );
    leanh::lean_dec(v_a_742_);
    leanh::lean_dec_ref(v_a_741_);
    leanh::lean_dec(v_a_740_);
    leanh::lean_dec_ref(v_a_739_);
    leanh::lean_dec(v_a_738_);
    leanh::lean_dec_ref(v_a_737_);
    leanh::lean_dec(v_a_736_);
    leanh::lean_dec_ref(v_a_735_);
    leanh::lean_dec(v_x_734_);
    return v_res_744_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1()
-> *mut leanh::LeanObject {
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_758_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__1;
    v___x_759_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___closed__3;
    v___x_760_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_761_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_757_, v___x_758_, v___x_759_, v___x_760_,
    );
    return v___x_761_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1___boxed(
    mut v_a_762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_763_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1();
    return v_res_763_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg___closed__0;
    v___x_767_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_767_, 0, v___x_766_);
    return v___x_767_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg___boxed(
    mut v_a_768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_769_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg();
    return v_res_769_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta(
    mut v_x_770_: *mut leanh::LeanObject,
    mut v_a_771_: *mut leanh::LeanObject,
    mut v_a_772_: *mut leanh::LeanObject,
    mut v_a_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
    mut v_a_775_: *mut leanh::LeanObject,
    mut v_a_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
    mut v_a_778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___redArg();
    return v___x_780_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___boxed(
    mut v_x_781_: *mut leanh::LeanObject,
    mut v_a_782_: *mut leanh::LeanObject,
    mut v_a_783_: *mut leanh::LeanObject,
    mut v_a_784_: *mut leanh::LeanObject,
    mut v_a_785_: *mut leanh::LeanObject,
    mut v_a_786_: *mut leanh::LeanObject,
    mut v_a_787_: *mut leanh::LeanObject,
    mut v_a_788_: *mut leanh::LeanObject,
    mut v_a_789_: *mut leanh::LeanObject,
    mut v_a_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ =
        l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta(
            v_x_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_,
            v_a_789_,
        );
    leanh::lean_dec(v_a_789_);
    leanh::lean_dec_ref(v_a_788_);
    leanh::lean_dec(v_a_787_);
    leanh::lean_dec_ref(v_a_786_);
    leanh::lean_dec(v_a_785_);
    leanh::lean_dec_ref(v_a_784_);
    leanh::lean_dec(v_a_783_);
    leanh::lean_dec_ref(v_a_782_);
    leanh::lean_dec(v_x_781_);
    return v_res_791_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1()
-> *mut leanh::LeanObject {
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_805_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__1;
    v___x_806_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___closed__3;
    v___x_807_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_808_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_804_, v___x_805_, v___x_806_, v___x_807_,
    );
    return v___x_808_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1___boxed(
    mut v_a_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1();
    return v_res_810_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg___closed__0;
    v___x_814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_814_, 0, v___x_813_);
    return v___x_814_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg___boxed(
    mut v_a_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg();
    return v_res_816_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch(
    mut v_x_817_: *mut leanh::LeanObject,
    mut v_a_818_: *mut leanh::LeanObject,
    mut v_a_819_: *mut leanh::LeanObject,
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_a_823_: *mut leanh::LeanObject,
    mut v_a_824_: *mut leanh::LeanObject,
    mut v_a_825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___redArg();
    return v___x_827_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___boxed(
    mut v_x_828_: *mut leanh::LeanObject,
    mut v_a_829_: *mut leanh::LeanObject,
    mut v_a_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
    mut v_a_832_: *mut leanh::LeanObject,
    mut v_a_833_: *mut leanh::LeanObject,
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
    mut v_a_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch(v_x_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
    leanh::lean_dec(v_a_836_);
    leanh::lean_dec_ref(v_a_835_);
    leanh::lean_dec(v_a_834_);
    leanh::lean_dec_ref(v_a_833_);
    leanh::lean_dec(v_a_832_);
    leanh::lean_dec_ref(v_a_831_);
    leanh::lean_dec(v_a_830_);
    leanh::lean_dec_ref(v_a_829_);
    leanh::lean_dec(v_x_828_);
    return v_res_838_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1()
-> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_852_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__1;
    v___x_853_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___closed__3;
    v___x_854_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_855_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_851_, v___x_852_, v___x_853_, v___x_854_,
    );
    return v___x_855_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1___boxed(
    mut v_a_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_857_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1();
    return v_res_857_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg___closed__0;
    v___x_861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_861_, 0, v___x_860_);
    return v___x_861_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg___boxed(
    mut v_a_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_863_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg();
    return v_res_863_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj(
    mut v_x_864_: *mut leanh::LeanObject,
    mut v_a_865_: *mut leanh::LeanObject,
    mut v_a_866_: *mut leanh::LeanObject,
    mut v_a_867_: *mut leanh::LeanObject,
    mut v_a_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_a_871_: *mut leanh::LeanObject,
    mut v_a_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___redArg();
    return v___x_874_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___boxed(
    mut v_x_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
    mut v_a_877_: *mut leanh::LeanObject,
    mut v_a_878_: *mut leanh::LeanObject,
    mut v_a_879_: *mut leanh::LeanObject,
    mut v_a_880_: *mut leanh::LeanObject,
    mut v_a_881_: *mut leanh::LeanObject,
    mut v_a_882_: *mut leanh::LeanObject,
    mut v_a_883_: *mut leanh::LeanObject,
    mut v_a_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_885_ =
        l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj(
            v_x_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_,
            v_a_883_,
        );
    leanh::lean_dec(v_a_883_);
    leanh::lean_dec_ref(v_a_882_);
    leanh::lean_dec(v_a_881_);
    leanh::lean_dec_ref(v_a_880_);
    leanh::lean_dec(v_a_879_);
    leanh::lean_dec_ref(v_a_878_);
    leanh::lean_dec(v_a_877_);
    leanh::lean_dec_ref(v_a_876_);
    leanh::lean_dec(v_x_875_);
    return v_res_885_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1()
-> *mut leanh::LeanObject {
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_898_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_899_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__1;
    v___x_900_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___closed__3;
    v___x_901_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_902_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_898_, v___x_899_, v___x_900_, v___x_901_,
    );
    return v___x_902_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1___boxed(
    mut v_a_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1();
    return v_res_904_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0(
    mut v_x_907_: *mut leanh::LeanObject,
    mut v___y_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
    mut v___y_911_: *mut leanh::LeanObject,
    mut v___y_912_: *mut leanh::LeanObject,
    mut v___y_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0___closed__0;
    v___x_919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_919_, 0, v___x_918_);
    return v___x_919_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0___boxed(
    mut v_x_920_: *mut leanh::LeanObject,
    mut v___y_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
    mut v___y_925_: *mut leanh::LeanObject,
    mut v___y_926_: *mut leanh::LeanObject,
    mut v___y_927_: *mut leanh::LeanObject,
    mut v___y_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___lam__0(v_x_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
    leanh::lean_dec(v___y_929_);
    leanh::lean_dec_ref(v___y_928_);
    leanh::lean_dec(v___y_927_);
    leanh::lean_dec_ref(v___y_926_);
    leanh::lean_dec(v___y_925_);
    leanh::lean_dec_ref(v___y_924_);
    leanh::lean_dec(v___y_923_);
    leanh::lean_dec(v___y_922_);
    leanh::lean_dec(v___y_921_);
    leanh::lean_dec_ref(v_x_920_);
    return v_res_931_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg()
-> *mut leanh::LeanObject {
    let mut v___f_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_934_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___closed__0;
    v___x_935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_935_, 0, v___f_934_);
    return v___x_935_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg___boxed(
    mut v_a_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_937_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg();
    return v_res_937_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone(
    mut v_x_938_: *mut leanh::LeanObject,
    mut v_a_939_: *mut leanh::LeanObject,
    mut v_a_940_: *mut leanh::LeanObject,
    mut v_a_941_: *mut leanh::LeanObject,
    mut v_a_942_: *mut leanh::LeanObject,
    mut v_a_943_: *mut leanh::LeanObject,
    mut v_a_944_: *mut leanh::LeanObject,
    mut v_a_945_: *mut leanh::LeanObject,
    mut v_a_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_948_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___redArg();
    return v___x_948_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___boxed(
    mut v_x_949_: *mut leanh::LeanObject,
    mut v_a_950_: *mut leanh::LeanObject,
    mut v_a_951_: *mut leanh::LeanObject,
    mut v_a_952_: *mut leanh::LeanObject,
    mut v_a_953_: *mut leanh::LeanObject,
    mut v_a_954_: *mut leanh::LeanObject,
    mut v_a_955_: *mut leanh::LeanObject,
    mut v_a_956_: *mut leanh::LeanObject,
    mut v_a_957_: *mut leanh::LeanObject,
    mut v_a_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_959_ =
        l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone(
            v_x_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_,
            v_a_957_,
        );
    leanh::lean_dec(v_a_957_);
    leanh::lean_dec_ref(v_a_956_);
    leanh::lean_dec(v_a_955_);
    leanh::lean_dec_ref(v_a_954_);
    leanh::lean_dec(v_a_953_);
    leanh::lean_dec_ref(v_a_952_);
    leanh::lean_dec(v_a_951_);
    leanh::lean_dec_ref(v_a_950_);
    leanh::lean_dec(v_x_949_);
    return v_res_959_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1()
-> *mut leanh::LeanObject {
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_973_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__1;
    v___x_974_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___closed__3;
    v___x_975_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_976_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_972_, v___x_973_, v___x_974_, v___x_975_,
    );
    return v___x_976_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1___boxed(
    mut v_a_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1();
    return v_res_978_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ = leanh::lean_box(0);
    v___x_980_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_981_, 0, v___x_980_);
    leanh::lean_ctor_set(v___x_981_, 1, v___x_979_);
    return v___x_981_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___closed__0);
    v___x_984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_984_, 0, v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg___boxed(
    mut v___y_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg();
    return v_res_986_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0(
    mut v_00_u03b1_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
    mut v___y_991_: *mut leanh::LeanObject,
    mut v___y_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_997_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg();
    return v___x_997_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___boxed(
    mut v_00_u03b1_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0(v_00_u03b1_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
    leanh::lean_dec(v___y_1006_);
    leanh::lean_dec_ref(v___y_1005_);
    leanh::lean_dec(v___y_1004_);
    leanh::lean_dec_ref(v___y_1003_);
    leanh::lean_dec(v___y_1002_);
    leanh::lean_dec_ref(v___y_1001_);
    leanh::lean_dec(v___y_1000_);
    leanh::lean_dec_ref(v___y_999_);
    return v_res_1008_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___lam__0(
    mut v_a_1009_: *mut leanh::LeanObject,
    mut v_a_1010_: *mut leanh::LeanObject,
    mut v___y_1011_: *mut leanh::LeanObject,
    mut v___y_1012_: *mut leanh::LeanObject,
    mut v___y_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1024_: u8 = 0;
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1026_: u8 = 0;
    let mut v_e_x27_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1030_: u8 = 0;
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v_done_1036_: u8 = 0;
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut v_unused_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1020_);
                leanh::lean_inc_ref(v___y_1019_);
                leanh::lean_inc(v___y_1018_);
                leanh::lean_inc_ref(v___y_1017_);
                leanh::lean_inc(v___y_1016_);
                leanh::lean_inc_ref(v___y_1015_);
                leanh::lean_inc(v___y_1014_);
                leanh::lean_inc(v___y_1013_);
                leanh::lean_inc(v___y_1012_);
                leanh::lean_inc_ref(v___y_1011_);
                v___x_1022_ = leanh::lean_apply_11(
                    v_a_1009_,
                    v___y_1011_,
                    v___y_1012_,
                    v___y_1013_,
                    v___y_1014_,
                    v___y_1015_,
                    v___y_1016_,
                    v___y_1017_,
                    v___y_1018_,
                    v___y_1019_,
                    v___y_1020_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1022_) == 0 {
                    v_a_1023_ = leanh::lean_ctor_get(v___x_1022_, 0);
                    leanh::lean_inc(v_a_1023_);
                    if leanh::lean_obj_tag(v_a_1023_) == 0 {
                        v_done_1024_ = leanh::lean_ctor_get_uint8(v_a_1023_, 0 as u32);
                        leanh::lean_dec_ref_known(v_a_1023_, 0);
                        if v_done_1024_ == 0 {
                            leanh::lean_dec_ref_known(v___x_1022_, 1);
                            v___x_1025_ = leanh::lean_apply_11(
                                v_a_1010_,
                                v___y_1011_,
                                v___y_1012_,
                                v___y_1013_,
                                v___y_1014_,
                                v___y_1015_,
                                v___y_1016_,
                                v___y_1017_,
                                v___y_1018_,
                                v___y_1019_,
                                v___y_1020_,
                                leanh::lean_box(0),
                            );
                            return v___x_1025_;
                        } else {
                            leanh::lean_dec(v___y_1020_);
                            leanh::lean_dec_ref(v___y_1019_);
                            leanh::lean_dec(v___y_1018_);
                            leanh::lean_dec_ref(v___y_1017_);
                            leanh::lean_dec(v___y_1016_);
                            leanh::lean_dec_ref(v___y_1015_);
                            leanh::lean_dec(v___y_1014_);
                            leanh::lean_dec(v___y_1013_);
                            leanh::lean_dec(v___y_1012_);
                            leanh::lean_dec_ref(v___y_1011_);
                            leanh::lean_dec_ref(v_a_1010_);
                            return v___x_1022_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_1011_);
                        v_done_1026_ = leanh::lean_ctor_get_uint8(
                            v_a_1023_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_done_1026_ == 0 {
                            leanh::lean_dec_ref_known(v___x_1022_, 1);
                            v_e_x27_1027_ = leanh::lean_ctor_get(v_a_1023_, 0);
                            v_isSharedCheck_1045_ =
                                (!leanh::lean_is_exclusive(v_a_1023_)) as u8;
                            if v_isSharedCheck_1045_ == 0 {
                                v___x_1029_ = v_a_1023_;
                                v_isShared_1030_ = v_isSharedCheck_1045_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_e_x27_1027_);
                                leanh::lean_dec(v_a_1023_);
                                v___x_1029_ = leanh::lean_box(0);
                                v_isShared_1030_ = v_isSharedCheck_1045_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_a_1023_, 1);
                            leanh::lean_dec(v___y_1020_);
                            leanh::lean_dec_ref(v___y_1019_);
                            leanh::lean_dec(v___y_1018_);
                            leanh::lean_dec_ref(v___y_1017_);
                            leanh::lean_dec(v___y_1016_);
                            leanh::lean_dec_ref(v___y_1015_);
                            leanh::lean_dec(v___y_1014_);
                            leanh::lean_dec(v___y_1013_);
                            leanh::lean_dec(v___y_1012_);
                            leanh::lean_dec_ref(v_a_1010_);
                            return v___x_1022_;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1020_);
                    leanh::lean_dec_ref(v___y_1019_);
                    leanh::lean_dec(v___y_1018_);
                    leanh::lean_dec_ref(v___y_1017_);
                    leanh::lean_dec(v___y_1016_);
                    leanh::lean_dec_ref(v___y_1015_);
                    leanh::lean_dec(v___y_1014_);
                    leanh::lean_dec(v___y_1013_);
                    leanh::lean_dec(v___y_1012_);
                    leanh::lean_dec_ref(v___y_1011_);
                    leanh::lean_dec_ref(v_a_1010_);
                    return v___x_1022_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_e_x27_1027_);
                v___x_1031_ = leanh::lean_apply_11(
                    v_a_1010_,
                    v_e_x27_1027_,
                    v___y_1012_,
                    v___y_1013_,
                    v___y_1014_,
                    v___y_1015_,
                    v___y_1016_,
                    v___y_1017_,
                    v___y_1018_,
                    v___y_1019_,
                    v___y_1020_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1031_) == 0 {
                    v_a_1032_ = leanh::lean_ctor_get(v___x_1031_, 0);
                    leanh::lean_inc(v_a_1032_);
                    if leanh::lean_obj_tag(v_a_1032_) == 0 {
                        v_isSharedCheck_1043_ =
                            (!leanh::lean_is_exclusive(v___x_1031_)) as u8;
                        if v_isSharedCheck_1043_ == 0 {
                            v_unused_1044_ = leanh::lean_ctor_get(v___x_1031_, 0);
                            leanh::lean_dec(v_unused_1044_);
                            v___x_1034_ = v___x_1031_;
                            v_isShared_1035_ = v_isSharedCheck_1043_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1031_);
                            v___x_1034_ = leanh::lean_box(0);
                            v_isShared_1035_ = v_isSharedCheck_1043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_1032_, 1);
                        leanh::lean_del_object(v___x_1029_);
                        leanh::lean_dec_ref(v_e_x27_1027_);
                        return v___x_1031_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1029_);
                    leanh::lean_dec_ref(v_e_x27_1027_);
                    return v___x_1031_;
                }
            }
            2 => {
                v_done_1036_ = leanh::lean_ctor_get_uint8(v_a_1032_, 0 as u32);
                leanh::lean_dec_ref_known(v_a_1032_, 0);
                if v_isShared_1030_ == 0 {
                    v___x_1038_ = v___x_1029_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_e_x27_1027_);
                    v___x_1038_ = v_reuseFailAlloc_1042_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1038_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_done_1036_,
                );
                if v_isShared_1035_ == 0 {
                    leanh::lean_ctor_set(v___x_1034_, 0, v___x_1038_);
                    v___x_1040_ = v___x_1034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
                    v___x_1040_ = v_reuseFailAlloc_1041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___lam__0___boxed(
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v___y_1048_: *mut leanh::LeanObject,
    mut v___y_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
    mut v___y_1051_: *mut leanh::LeanObject,
    mut v___y_1052_: *mut leanh::LeanObject,
    mut v___y_1053_: *mut leanh::LeanObject,
    mut v___y_1054_: *mut leanh::LeanObject,
    mut v___y_1055_: *mut leanh::LeanObject,
    mut v___y_1056_: *mut leanh::LeanObject,
    mut v___y_1057_: *mut leanh::LeanObject,
    mut v___y_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1059_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___lam__0(v_a_1046_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
    return v_res_1059_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen(
    mut v_stx_1067_: *mut leanh::LeanObject,
    mut v_a_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_a_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v___f_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1077_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1;
                leanh::lean_inc(v_stx_1067_);
                v___x_1078_ = l_Lean_Syntax_isOfKind(v_stx_1067_, v___x_1077_);
                if v___x_1078_ == 0 {
                    leanh::lean_dec(v_stx_1067_);
                    v___x_1079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg();
                    return v___x_1079_;
                } else {
                    v___x_1080_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1081_ = l_Lean_Syntax_getArg(v_stx_1067_, v___x_1080_);
                    v___x_1082_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
                        v___x_1081_,
                        v_a_1068_,
                        v_a_1069_,
                        v_a_1070_,
                        v_a_1071_,
                        v_a_1072_,
                        v_a_1073_,
                        v_a_1074_,
                        v_a_1075_,
                    );
                    if leanh::lean_obj_tag(v___x_1082_) == 0 {
                        v_a_1083_ = leanh::lean_ctor_get(v___x_1082_, 0);
                        leanh::lean_inc(v_a_1083_);
                        leanh::lean_dec_ref_known(v___x_1082_, 1);
                        v___x_1084_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1085_ = l_Lean_Syntax_getArg(v_stx_1067_, v___x_1084_);
                        leanh::lean_dec(v_stx_1067_);
                        v___x_1086_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
                            v___x_1085_,
                            v_a_1068_,
                            v_a_1069_,
                            v_a_1070_,
                            v_a_1071_,
                            v_a_1072_,
                            v_a_1073_,
                            v_a_1074_,
                            v_a_1075_,
                        );
                        if leanh::lean_obj_tag(v___x_1086_) == 0 {
                            v_a_1087_ = leanh::lean_ctor_get(v___x_1086_, 0);
                            v_isSharedCheck_1095_ =
                                (!leanh::lean_is_exclusive(v___x_1086_)) as u8;
                            if v_isSharedCheck_1095_ == 0 {
                                v___x_1089_ = v___x_1086_;
                                v_isShared_1090_ = v_isSharedCheck_1095_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1087_);
                                leanh::lean_dec(v___x_1086_);
                                v___x_1089_ = leanh::lean_box(0);
                                v_isShared_1090_ = v_isSharedCheck_1095_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1083_);
                            return v___x_1086_;
                        }
                    } else {
                        leanh::lean_dec(v_stx_1067_);
                        return v___x_1082_;
                    }
                }
            }
            1 => {
                v___f_1091_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                leanh::lean_closure_set(v___f_1091_, 0, v_a_1083_);
                leanh::lean_closure_set(v___f_1091_, 1, v_a_1087_);
                if v_isShared_1090_ == 0 {
                    leanh::lean_ctor_set(v___x_1089_, 0, v___f_1091_);
                    v___x_1093_ = v___x_1089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___f_1091_);
                    v___x_1093_ = v_reuseFailAlloc_1094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___boxed(
    mut v_stx_1096_: *mut leanh::LeanObject,
    mut v_a_1097_: *mut leanh::LeanObject,
    mut v_a_1098_: *mut leanh::LeanObject,
    mut v_a_1099_: *mut leanh::LeanObject,
    mut v_a_1100_: *mut leanh::LeanObject,
    mut v_a_1101_: *mut leanh::LeanObject,
    mut v_a_1102_: *mut leanh::LeanObject,
    mut v_a_1103_: *mut leanh::LeanObject,
    mut v_a_1104_: *mut leanh::LeanObject,
    mut v_a_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen(v_stx_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
    leanh::lean_dec(v_a_1104_);
    leanh::lean_dec_ref(v_a_1103_);
    leanh::lean_dec(v_a_1102_);
    leanh::lean_dec_ref(v_a_1101_);
    leanh::lean_dec(v_a_1100_);
    leanh::lean_dec_ref(v_a_1099_);
    leanh::lean_dec(v_a_1098_);
    leanh::lean_dec_ref(v_a_1097_);
    return v_res_1106_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1()
-> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_1113_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___closed__1;
    v___x_1114_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___closed__1;
    v___x_1115_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1116_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1112_,
        v___x_1113_,
        v___x_1114_,
        v___x_1115_,
    );
    return v___x_1116_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1___boxed(
    mut v_a_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1();
    return v_res_1118_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___lam__0(
    mut v_a_1119_: *mut leanh::LeanObject,
    mut v_a_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
    mut v___y_1122_: *mut leanh::LeanObject,
    mut v___y_1123_: *mut leanh::LeanObject,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
    mut v___y_1129_: *mut leanh::LeanObject,
    mut v___y_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1130_);
    leanh::lean_inc_ref(v___y_1129_);
    leanh::lean_inc(v___y_1128_);
    leanh::lean_inc_ref(v___y_1127_);
    leanh::lean_inc(v___y_1126_);
    leanh::lean_inc_ref(v___y_1125_);
    leanh::lean_inc(v___y_1124_);
    leanh::lean_inc(v___y_1123_);
    leanh::lean_inc(v___y_1122_);
    leanh::lean_inc_ref(v___y_1121_);
    v___x_1132_ = leanh::lean_apply_11(
        v_a_1119_,
        v___y_1121_,
        v___y_1122_,
        v___y_1123_,
        v___y_1124_,
        v___y_1125_,
        v___y_1126_,
        v___y_1127_,
        v___y_1128_,
        v___y_1129_,
        v___y_1130_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_1132_) == 0 {
        let mut v_a_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1133_ = leanh::lean_ctor_get(v___x_1132_, 0);
        leanh::lean_inc(v_a_1133_);
        if leanh::lean_obj_tag(v_a_1133_) == 0 {
            let mut v_done_1134_: u8 = 0;
            v_done_1134_ = leanh::lean_ctor_get_uint8(v_a_1133_, 0 as u32);
            leanh::lean_dec_ref_known(v_a_1133_, 0);
            if v_done_1134_ == 0 {
                let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_1132_, 1);
                v___x_1135_ = leanh::lean_apply_11(
                    v_a_1120_,
                    v___y_1121_,
                    v___y_1122_,
                    v___y_1123_,
                    v___y_1124_,
                    v___y_1125_,
                    v___y_1126_,
                    v___y_1127_,
                    v___y_1128_,
                    v___y_1129_,
                    v___y_1130_,
                    leanh::lean_box(0),
                );
                return v___x_1135_;
            } else {
                leanh::lean_dec(v___y_1130_);
                leanh::lean_dec_ref(v___y_1129_);
                leanh::lean_dec(v___y_1128_);
                leanh::lean_dec_ref(v___y_1127_);
                leanh::lean_dec(v___y_1126_);
                leanh::lean_dec_ref(v___y_1125_);
                leanh::lean_dec(v___y_1124_);
                leanh::lean_dec(v___y_1123_);
                leanh::lean_dec(v___y_1122_);
                leanh::lean_dec_ref(v___y_1121_);
                leanh::lean_dec_ref(v_a_1120_);
                return v___x_1132_;
            }
        } else {
            leanh::lean_dec_ref_known(v_a_1133_, 1);
            leanh::lean_dec(v___y_1130_);
            leanh::lean_dec_ref(v___y_1129_);
            leanh::lean_dec(v___y_1128_);
            leanh::lean_dec_ref(v___y_1127_);
            leanh::lean_dec(v___y_1126_);
            leanh::lean_dec_ref(v___y_1125_);
            leanh::lean_dec(v___y_1124_);
            leanh::lean_dec(v___y_1123_);
            leanh::lean_dec(v___y_1122_);
            leanh::lean_dec_ref(v___y_1121_);
            leanh::lean_dec_ref(v_a_1120_);
            return v___x_1132_;
        }
    } else {
        leanh::lean_dec(v___y_1130_);
        leanh::lean_dec_ref(v___y_1129_);
        leanh::lean_dec(v___y_1128_);
        leanh::lean_dec_ref(v___y_1127_);
        leanh::lean_dec(v___y_1126_);
        leanh::lean_dec_ref(v___y_1125_);
        leanh::lean_dec(v___y_1124_);
        leanh::lean_dec(v___y_1123_);
        leanh::lean_dec(v___y_1122_);
        leanh::lean_dec_ref(v___y_1121_);
        leanh::lean_dec_ref(v_a_1120_);
        return v___x_1132_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___lam__0___boxed(
    mut v_a_1136_: *mut leanh::LeanObject,
    mut v_a_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
    mut v___y_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___lam__0(v_a_1136_, v_a_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
    return v_res_1149_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse(
    mut v_stx_1157_: *mut leanh::LeanObject,
    mut v_a_1158_: *mut leanh::LeanObject,
    mut v_a_1159_: *mut leanh::LeanObject,
    mut v_a_1160_: *mut leanh::LeanObject,
    mut v_a_1161_: *mut leanh::LeanObject,
    mut v_a_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v___f_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1167_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1;
                leanh::lean_inc(v_stx_1157_);
                v___x_1168_ = l_Lean_Syntax_isOfKind(v_stx_1157_, v___x_1167_);
                if v___x_1168_ == 0 {
                    leanh::lean_dec(v_stx_1157_);
                    v___x_1169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg();
                    return v___x_1169_;
                } else {
                    v___x_1170_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1171_ = l_Lean_Syntax_getArg(v_stx_1157_, v___x_1170_);
                    v___x_1172_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
                        v___x_1171_,
                        v_a_1158_,
                        v_a_1159_,
                        v_a_1160_,
                        v_a_1161_,
                        v_a_1162_,
                        v_a_1163_,
                        v_a_1164_,
                        v_a_1165_,
                    );
                    if leanh::lean_obj_tag(v___x_1172_) == 0 {
                        v_a_1173_ = leanh::lean_ctor_get(v___x_1172_, 0);
                        leanh::lean_inc(v_a_1173_);
                        leanh::lean_dec_ref_known(v___x_1172_, 1);
                        v___x_1174_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1175_ = l_Lean_Syntax_getArg(v_stx_1157_, v___x_1174_);
                        leanh::lean_dec(v_stx_1157_);
                        v___x_1176_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
                            v___x_1175_,
                            v_a_1158_,
                            v_a_1159_,
                            v_a_1160_,
                            v_a_1161_,
                            v_a_1162_,
                            v_a_1163_,
                            v_a_1164_,
                            v_a_1165_,
                        );
                        if leanh::lean_obj_tag(v___x_1176_) == 0 {
                            v_a_1177_ = leanh::lean_ctor_get(v___x_1176_, 0);
                            v_isSharedCheck_1185_ =
                                (!leanh::lean_is_exclusive(v___x_1176_)) as u8;
                            if v_isSharedCheck_1185_ == 0 {
                                v___x_1179_ = v___x_1176_;
                                v_isShared_1180_ = v_isSharedCheck_1185_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1177_);
                                leanh::lean_dec(v___x_1176_);
                                v___x_1179_ = leanh::lean_box(0);
                                v_isShared_1180_ = v_isSharedCheck_1185_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1173_);
                            return v___x_1176_;
                        }
                    } else {
                        leanh::lean_dec(v_stx_1157_);
                        return v___x_1172_;
                    }
                }
            }
            1 => {
                v___f_1181_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                leanh::lean_closure_set(v___f_1181_, 0, v_a_1173_);
                leanh::lean_closure_set(v___f_1181_, 1, v_a_1177_);
                if v_isShared_1180_ == 0 {
                    leanh::lean_ctor_set(v___x_1179_, 0, v___f_1181_);
                    v___x_1183_ = v___x_1179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___f_1181_);
                    v___x_1183_ = v_reuseFailAlloc_1184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___boxed(
    mut v_stx_1186_: *mut leanh::LeanObject,
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_a_1188_: *mut leanh::LeanObject,
    mut v_a_1189_: *mut leanh::LeanObject,
    mut v_a_1190_: *mut leanh::LeanObject,
    mut v_a_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse(v_stx_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
    leanh::lean_dec(v_a_1194_);
    leanh::lean_dec_ref(v_a_1193_);
    leanh::lean_dec(v_a_1192_);
    leanh::lean_dec_ref(v_a_1191_);
    leanh::lean_dec(v_a_1190_);
    leanh::lean_dec_ref(v_a_1189_);
    leanh::lean_dec(v_a_1188_);
    leanh::lean_dec_ref(v_a_1187_);
    return v_res_1196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1()
-> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_1203_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___closed__1;
    v___x_1204_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___closed__1;
    v___x_1205_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1206_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1202_,
        v___x_1203_,
        v___x_1204_,
        v___x_1205_,
    );
    return v___x_1206_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1___boxed(
    mut v_a_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1();
    return v_res_1208_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen(
    mut v_stx_1216_: *mut leanh::LeanObject,
    mut v_a_1217_: *mut leanh::LeanObject,
    mut v_a_1218_: *mut leanh::LeanObject,
    mut v_a_1219_: *mut leanh::LeanObject,
    mut v_a_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
    mut v_a_1222_: *mut leanh::LeanObject,
    mut v_a_1223_: *mut leanh::LeanObject,
    mut v_a_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    v___x_1226_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1;
    leanh::lean_inc(v_stx_1216_);
    v___x_1227_ = l_Lean_Syntax_isOfKind(v_stx_1216_, v___x_1226_);
    if v___x_1227_ == 0 {
        let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_1216_);
        v___x_1228_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen_spec__0___redArg();
        return v___x_1228_;
    } else {
        let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1229_ = leanh::lean_unsigned_to_nat(1);
        v___x_1230_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1229_);
        leanh::lean_dec(v_stx_1216_);
        v___x_1231_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
            v___x_1230_,
            v_a_1217_,
            v_a_1218_,
            v_a_1219_,
            v_a_1220_,
            v_a_1221_,
            v_a_1222_,
            v_a_1223_,
            v_a_1224_,
        );
        return v___x_1231_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___boxed(
    mut v_stx_1232_: *mut leanh::LeanObject,
    mut v_a_1233_: *mut leanh::LeanObject,
    mut v_a_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
    mut v_a_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1242_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen(v_stx_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
    leanh::lean_dec(v_a_1240_);
    leanh::lean_dec_ref(v_a_1239_);
    leanh::lean_dec(v_a_1238_);
    leanh::lean_dec_ref(v_a_1237_);
    leanh::lean_dec(v_a_1236_);
    leanh::lean_dec_ref(v_a_1235_);
    leanh::lean_dec(v_a_1234_);
    leanh::lean_dec_ref(v_a_1233_);
    return v_res_1242_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1()
-> *mut leanh::LeanObject {
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
    v___x_1249_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___closed__1;
    v___x_1250_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___closed__1;
    v___x_1251_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1252_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1248_,
        v___x_1249_,
        v___x_1250_,
        v___x_1251_,
    );
    return v___x_1252_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1___boxed(
    mut v_a_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1();
    return v_res_1254_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZetaDeltaAll__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabZeta__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabBeta__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabReduceMatch__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabProj__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabNone__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocAndThen__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocOrElse__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDSimprocParen__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(builtin);
}