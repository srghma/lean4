// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Rewrite
// Imports: Lean.Elab.Tactic.Rewrite Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr5, l_Lean_Syntax_getArg};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_getLhs___redArg,
    l_Lean_Elab_Tactic_Conv_updateLhs, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Rewrite::{
    initialize_Lean_Elab_Tactic_Rewrite, l_Lean_Elab_Tactic_elabRewrite,
    l_Lean_Elab_Tactic_elabRewriteConfig___redArg, l_Lean_Elab_Tactic_finishElabRewrite,
    l_Lean_Elab_Tactic_withRWRulesSeq, runtime_initialize_Lean_Elab_Tactic_Rewrite,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            258 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 119, 114, 105, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4_value) as *mut LeanObject,779923751473675077 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 82, 101, 119, 114, 105, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7_value) as *mut LeanObject,18206475929533717790 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0_value) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1_value) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 65 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3_value) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4_value) as *mut LeanObject,((( 65 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(
    mut v___y_250_: *mut LeanObject,
    mut v_term_251_: *mut LeanObject,
    mut v_symm_252_: u8,
    mut v_a_253_: *mut LeanObject,
    mut v___y_254_: *mut LeanObject,
    mut v___y_255_: *mut LeanObject,
    mut v___y_256_: *mut LeanObject,
    mut v___y_257_: *mut LeanObject,
    mut v___y_258_: *mut LeanObject,
    mut v___y_259_: *mut LeanObject,
    mut v___y_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_270_: u8 = 0;
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_274_: u8 = 0;
    let mut v_a_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_278_: u8 = 0;
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_262_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_250_, v___y_257_, v___y_258_, v___y_259_, v___y_260_,
                );
                if lean_obj_tag(v___x_262_) == 0 {
                    v_a_263_ = lean_ctor_get(v___x_262_, 0);
                    lean_inc(v_a_263_);
                    lean_dec_ref_known(v___x_262_, 1);
                    v___x_264_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_250_, v___y_257_, v___y_258_, v___y_259_, v___y_260_,
                    );
                    if lean_obj_tag(v___x_264_) == 0 {
                        v_a_265_ = lean_ctor_get(v___x_264_, 0);
                        lean_inc(v_a_265_);
                        lean_dec_ref_known(v___x_264_, 1);
                        v___x_266_ = l_Lean_Elab_Tactic_elabRewrite(
                            v_a_263_,
                            v_a_265_,
                            v_term_251_,
                            v_symm_252_,
                            v_a_253_,
                            v___y_254_,
                            v___y_250_,
                            v___y_255_,
                            v___y_256_,
                            v___y_257_,
                            v___y_258_,
                            v___y_259_,
                            v___y_260_,
                        );
                        return v___x_266_;
                    } else {
                        lean_dec(v_a_263_);
                        lean_dec_ref(v_a_253_);
                        lean_dec(v_term_251_);
                        v_a_267_ = lean_ctor_get(v___x_264_, 0);
                        v_isSharedCheck_274_ = (!lean_is_exclusive(v___x_264_)) as u8;
                        if v_isSharedCheck_274_ == 0 {
                            v___x_269_ = v___x_264_;
                            v_isShared_270_ = v_isSharedCheck_274_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_267_);
                            lean_dec(v___x_264_);
                            v___x_269_ = lean_box(0);
                            v_isShared_270_ = v_isSharedCheck_274_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_253_);
                    lean_dec(v_term_251_);
                    v_a_275_ = lean_ctor_get(v___x_262_, 0);
                    v_isSharedCheck_282_ = (!lean_is_exclusive(v___x_262_)) as u8;
                    if v_isSharedCheck_282_ == 0 {
                        v___x_277_ = v___x_262_;
                        v_isShared_278_ = v_isSharedCheck_282_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_275_);
                        lean_dec(v___x_262_);
                        v___x_277_ = lean_box(0);
                        v_isShared_278_ = v_isSharedCheck_282_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_270_ == 0 {
                    v___x_272_ = v___x_269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
                    v___x_272_ = v_reuseFailAlloc_273_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_272_;
            }
            3 => {
                if v_isShared_278_ == 0 {
                    v___x_280_ = v___x_277_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
                    v___x_280_ = v_reuseFailAlloc_281_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed(
    mut v___y_283_: *mut LeanObject,
    mut v_term_284_: *mut LeanObject,
    mut v_symm_285_: *mut LeanObject,
    mut v_a_286_: *mut LeanObject,
    mut v___y_287_: *mut LeanObject,
    mut v___y_288_: *mut LeanObject,
    mut v___y_289_: *mut LeanObject,
    mut v___y_290_: *mut LeanObject,
    mut v___y_291_: *mut LeanObject,
    mut v___y_292_: *mut LeanObject,
    mut v___y_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_295_: u8 = 0;
    let mut v_res_296_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_295_ = (lean_unbox(v_symm_285_) as u8);
    v_res_296_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(
        v___y_283_,
        v_term_284_,
        v_symm_boxed_295_,
        v_a_286_,
        v___y_287_,
        v___y_288_,
        v___y_289_,
        v___y_290_,
        v___y_291_,
        v___y_292_,
        v___y_293_,
    );
    lean_dec(v___y_293_);
    lean_dec_ref(v___y_292_);
    lean_dec(v___y_291_);
    lean_dec_ref(v___y_290_);
    lean_dec(v___y_289_);
    lean_dec_ref(v___y_288_);
    lean_dec_ref(v___y_287_);
    lean_dec(v___y_283_);
    return v_res_296_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(
    mut v_term_297_: *mut LeanObject,
    mut v_symm_298_: u8,
    mut v_a_299_: *mut LeanObject,
    mut v___x_300_: u8,
    mut v___y_301_: *mut LeanObject,
    mut v___y_302_: *mut LeanObject,
    mut v___y_303_: *mut LeanObject,
    mut v___y_304_: *mut LeanObject,
    mut v___y_305_: *mut LeanObject,
    mut v___y_306_: *mut LeanObject,
    mut v___y_307_: *mut LeanObject,
    mut v___y_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_327_: u8 = 0;
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_331_: u8 = 0;
    let mut v_a_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_335_: u8 = 0;
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_339_: u8 = 0;
    let mut v_a_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_343_: u8 = 0;
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_310_ = lean_box((v_symm_298_) as usize);
                lean_inc_ref(v___y_301_);
                lean_inc(v___y_302_);
                v___f_311_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___f_311_, 0, v___y_302_);
                lean_closure_set(v___f_311_, 1, v_term_297_);
                lean_closure_set(v___f_311_, 2, v___x_310_);
                lean_closure_set(v___f_311_, 3, v_a_299_);
                lean_closure_set(v___f_311_, 4, v___y_301_);
                v___x_312_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___f_311_,
                        v___x_300_,
                        v___y_303_,
                        v___y_304_,
                        v___y_305_,
                        v___y_306_,
                        v___y_307_,
                        v___y_308_,
                    );
                if lean_obj_tag(v___x_312_) == 0 {
                    v_a_313_ = lean_ctor_get(v___x_312_, 0);
                    lean_inc(v_a_313_);
                    lean_dec_ref_known(v___x_312_, 1);
                    v___x_314_ = l_Lean_Elab_Tactic_finishElabRewrite(
                        v_a_313_, v___y_305_, v___y_306_, v___y_307_, v___y_308_,
                    );
                    if lean_obj_tag(v___x_314_) == 0 {
                        v_a_315_ = lean_ctor_get(v___x_314_, 0);
                        lean_inc(v_a_315_);
                        lean_dec_ref_known(v___x_314_, 1);
                        v_eNew_316_ = lean_ctor_get(v_a_315_, 0);
                        lean_inc_ref(v_eNew_316_);
                        v_eqProof_317_ = lean_ctor_get(v_a_315_, 1);
                        lean_inc_ref(v_eqProof_317_);
                        v_mvarIds_318_ = lean_ctor_get(v_a_315_, 2);
                        lean_inc(v_mvarIds_318_);
                        lean_dec(v_a_315_);
                        v___x_319_ = l_Lean_Elab_Tactic_Conv_updateLhs(
                            v_eNew_316_,
                            v_eqProof_317_,
                            v___y_301_,
                            v___y_302_,
                            v___y_303_,
                            v___y_304_,
                            v___y_305_,
                            v___y_306_,
                            v___y_307_,
                            v___y_308_,
                        );
                        lean_dec_ref(v___y_301_);
                        if lean_obj_tag(v___x_319_) == 0 {
                            lean_dec_ref_known(v___x_319_, 1);
                            v___x_320_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v___y_302_, v___y_305_, v___y_306_, v___y_307_, v___y_308_,
                            );
                            if lean_obj_tag(v___x_320_) == 0 {
                                v_a_321_ = lean_ctor_get(v___x_320_, 0);
                                lean_inc(v_a_321_);
                                lean_dec_ref_known(v___x_320_, 1);
                                v___x_322_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_322_, 0, v_a_321_);
                                lean_ctor_set(v___x_322_, 1, v_mvarIds_318_);
                                v___x_323_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                    v___x_322_, v___y_302_, v___y_305_, v___y_306_, v___y_307_,
                                    v___y_308_,
                                );
                                lean_dec(v___y_302_);
                                return v___x_323_;
                            } else {
                                lean_dec(v_mvarIds_318_);
                                lean_dec(v___y_302_);
                                v_a_324_ = lean_ctor_get(v___x_320_, 0);
                                v_isSharedCheck_331_ = (!lean_is_exclusive(v___x_320_)) as u8;
                                if v_isSharedCheck_331_ == 0 {
                                    v___x_326_ = v___x_320_;
                                    v_isShared_327_ = v_isSharedCheck_331_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_324_);
                                    lean_dec(v___x_320_);
                                    v___x_326_ = lean_box(0);
                                    v_isShared_327_ = v_isSharedCheck_331_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_mvarIds_318_);
                            lean_dec(v___y_302_);
                            return v___x_319_;
                        }
                    } else {
                        lean_dec(v___y_302_);
                        lean_dec_ref(v___y_301_);
                        v_a_332_ = lean_ctor_get(v___x_314_, 0);
                        v_isSharedCheck_339_ = (!lean_is_exclusive(v___x_314_)) as u8;
                        if v_isSharedCheck_339_ == 0 {
                            v___x_334_ = v___x_314_;
                            v_isShared_335_ = v_isSharedCheck_339_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_332_);
                            lean_dec(v___x_314_);
                            v___x_334_ = lean_box(0);
                            v_isShared_335_ = v_isSharedCheck_339_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_302_);
                    lean_dec_ref(v___y_301_);
                    v_a_340_ = lean_ctor_get(v___x_312_, 0);
                    v_isSharedCheck_347_ = (!lean_is_exclusive(v___x_312_)) as u8;
                    if v_isSharedCheck_347_ == 0 {
                        v___x_342_ = v___x_312_;
                        v_isShared_343_ = v_isSharedCheck_347_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_340_);
                        lean_dec(v___x_312_);
                        v___x_342_ = lean_box(0);
                        v_isShared_343_ = v_isSharedCheck_347_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_327_ == 0 {
                    v___x_329_ = v___x_326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
                    v___x_329_ = v_reuseFailAlloc_330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_329_;
            }
            3 => {
                if v_isShared_335_ == 0 {
                    v___x_337_ = v___x_334_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
                    v___x_337_ = v_reuseFailAlloc_338_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_337_;
            }
            5 => {
                if v_isShared_343_ == 0 {
                    v___x_345_ = v___x_342_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
                    v___x_345_ = v_reuseFailAlloc_346_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed(
    mut v_term_348_: *mut LeanObject,
    mut v_symm_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
    mut v___x_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
    mut v___y_354_: *mut LeanObject,
    mut v___y_355_: *mut LeanObject,
    mut v___y_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
    mut v___y_359_: *mut LeanObject,
    mut v___y_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_361_: u8 = 0;
    let mut v___x_1094__boxed_362_: u8 = 0;
    let mut v_res_363_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_361_ = (lean_unbox(v_symm_349_) as u8);
    v___x_1094__boxed_362_ = (lean_unbox(v___x_351_) as u8);
    v_res_363_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(
        v_term_348_,
        v_symm_boxed_361_,
        v_a_350_,
        v___x_1094__boxed_362_,
        v___y_352_,
        v___y_353_,
        v___y_354_,
        v___y_355_,
        v___y_356_,
        v___y_357_,
        v___y_358_,
        v___y_359_,
    );
    lean_dec(v___y_359_);
    lean_dec_ref(v___y_358_);
    lean_dec(v___y_357_);
    lean_dec_ref(v___y_356_);
    lean_dec(v___y_355_);
    lean_dec_ref(v___y_354_);
    return v_res_363_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(
    mut v_a_364_: *mut LeanObject,
    mut v_symm_365_: u8,
    mut v_term_366_: *mut LeanObject,
    mut v___y_367_: *mut LeanObject,
    mut v___y_368_: *mut LeanObject,
    mut v___y_369_: *mut LeanObject,
    mut v___y_370_: *mut LeanObject,
    mut v___y_371_: *mut LeanObject,
    mut v___y_372_: *mut LeanObject,
    mut v___y_373_: *mut LeanObject,
    mut v___y_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = 1;
    v___x_377_ = lean_box((v_symm_365_) as usize);
    v___x_378_ = lean_box((v___x_376_) as usize);
    v___f_379_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    lean_closure_set(v___f_379_, 0, v_term_366_);
    lean_closure_set(v___f_379_, 1, v___x_377_);
    lean_closure_set(v___f_379_, 2, v_a_364_);
    lean_closure_set(v___f_379_, 3, v___x_378_);
    v___x_380_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_379_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_,
        v___y_373_, v___y_374_,
    );
    return v___x_380_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed(
    mut v_a_381_: *mut LeanObject,
    mut v_symm_382_: *mut LeanObject,
    mut v_term_383_: *mut LeanObject,
    mut v___y_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
    mut v___y_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
    mut v___y_388_: *mut LeanObject,
    mut v___y_389_: *mut LeanObject,
    mut v___y_390_: *mut LeanObject,
    mut v___y_391_: *mut LeanObject,
    mut v___y_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_393_: u8 = 0;
    let mut v_res_394_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_393_ = (lean_unbox(v_symm_382_) as u8);
    v_res_394_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(
        v_a_381_,
        v_symm_boxed_393_,
        v_term_383_,
        v___y_384_,
        v___y_385_,
        v___y_386_,
        v___y_387_,
        v___y_388_,
        v___y_389_,
        v___y_390_,
        v___y_391_,
    );
    lean_dec(v___y_391_);
    lean_dec_ref(v___y_390_);
    lean_dec(v___y_389_);
    lean_dec_ref(v___y_388_);
    lean_dec(v___y_387_);
    lean_dec_ref(v___y_386_);
    lean_dec(v___y_385_);
    lean_dec_ref(v___y_384_);
    return v_res_394_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite(
    mut v_stx_400_: *mut LeanObject,
    mut v_a_401_: *mut LeanObject,
    mut v_a_402_: *mut LeanObject,
    mut v_a_403_: *mut LeanObject,
    mut v_a_404_: *mut LeanObject,
    mut v_a_405_: *mut LeanObject,
    mut v_a_406_: *mut LeanObject,
    mut v_a_407_: *mut LeanObject,
    mut v_a_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: u8 = 0;
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_410_ = lean_unsigned_to_nat(1);
                v___x_411_ = l_Lean_Syntax_getArg(v_stx_400_, v___x_410_);
                v___x_412_ = 1;
                v___x_413_ = l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0;
                v___x_414_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(
                    v___x_411_, v___x_413_, v___x_412_, v_a_401_, v_a_407_, v_a_408_,
                );
                if lean_obj_tag(v___x_414_) == 0 {
                    v_a_415_ = lean_ctor_get(v___x_414_, 0);
                    lean_inc(v_a_415_);
                    lean_dec_ref_known(v___x_414_, 1);
                    v___f_416_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed
                            as *mut core::ffi::c_void,
                        12,
                        1,
                    );
                    lean_closure_set(v___f_416_, 0, v_a_415_);
                    v___x_417_ = lean_unsigned_to_nat(0);
                    v___x_418_ = l_Lean_Syntax_getArg(v_stx_400_, v___x_417_);
                    v___x_419_ = lean_unsigned_to_nat(2);
                    v___x_420_ = l_Lean_Syntax_getArg(v_stx_400_, v___x_419_);
                    v___x_421_ = l_Lean_Elab_Tactic_withRWRulesSeq(
                        v___x_418_, v___x_420_, v___f_416_, v_a_401_, v_a_402_, v_a_403_, v_a_404_,
                        v_a_405_, v_a_406_, v_a_407_, v_a_408_,
                    );
                    lean_dec(v___x_420_);
                    return v___x_421_;
                } else {
                    v_a_422_ = lean_ctor_get(v___x_414_, 0);
                    v_isSharedCheck_429_ = (!lean_is_exclusive(v___x_414_)) as u8;
                    if v_isSharedCheck_429_ == 0 {
                        v___x_424_ = v___x_414_;
                        v_isShared_425_ = v_isSharedCheck_429_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_422_);
                        lean_dec(v___x_414_);
                        v___x_424_ = lean_box(0);
                        v_isShared_425_ = v_isSharedCheck_429_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_425_ == 0 {
                    v___x_427_ = v___x_424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
                    v___x_427_ = v_reuseFailAlloc_428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalRewrite___boxed(
    mut v_stx_430_: *mut LeanObject,
    mut v_a_431_: *mut LeanObject,
    mut v_a_432_: *mut LeanObject,
    mut v_a_433_: *mut LeanObject,
    mut v_a_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_440_: *mut LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Lean_Elab_Tactic_Conv_evalRewrite(
        v_stx_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_,
    );
    lean_dec(v_a_438_);
    lean_dec_ref(v_a_437_);
    lean_dec(v_a_436_);
    lean_dec_ref(v_a_435_);
    lean_dec(v_a_434_);
    lean_dec_ref(v_a_433_);
    lean_dec(v_a_432_);
    lean_dec_ref(v_a_431_);
    lean_dec(v_stx_430_);
    return v_res_440_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1()
-> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_462_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5;
    v___x_463_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8;
    v___x_464_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalRewrite___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_465_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_461_, v___x_462_, v___x_463_, v___x_464_,
    );
    return v___x_465_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___boxed(
    mut v_a_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_467_: *mut LeanObject = core::ptr::null_mut();
    v_res_467_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
    return v_res_467_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3()
-> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8;
    v___x_495_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6;
    v___x_496_ = l_Lean_addBuiltinDeclarationRanges(v___x_494_, v___x_495_);
    return v___x_496_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___boxed(
    mut v_a_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_498_: *mut LeanObject = core::ptr::null_mut();
    v_res_498_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
    return v_res_498_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
}
