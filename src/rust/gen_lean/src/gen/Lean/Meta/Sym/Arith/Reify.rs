// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Reify
// Imports: Lean.Meta.Sym.Arith.Functions Lean.Meta.Sym.Arith.MonadVar Lean.Meta.Sym.LitValues
use crate::ffi::lean_nat_to_int;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___boxed;
use crate::r#gen::Lean::Meta::Sym::Arith::Functions::{
    initialize_Lean_Meta_Sym_Arith_Functions, l_Lean_Meta_Sym_Arith_getAddFn___redArg,
    l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg, l_Lean_Meta_Sym_Arith_getIntCastFn___redArg,
    l_Lean_Meta_Sym_Arith_getMulFn___redArg, l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg,
    l_Lean_Meta_Sym_Arith_getNatCastFn___redArg, l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg,
    l_Lean_Meta_Sym_Arith_getNegFn___redArg, l_Lean_Meta_Sym_Arith_getPowFn___redArg,
    l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg, l_Lean_Meta_Sym_Arith_getSubFn___redArg,
    runtime_initialize_Lean_Meta_Sym_Arith_Functions,
};
use crate::r#gen::Lean::Meta::Sym::Arith::MonadVar::{
    initialize_Lean_Meta_Sym_Arith_MonadVar, runtime_initialize_Lean_Meta_Sym_Arith_MonadVar,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::LitValues::{
    initialize_Lean_Meta_Sym_LitValues, l_Lean_Meta_Sym_getIntValue_x3f,
    l_Lean_Meta_Sym_getNatValue_x3f, runtime_initialize_Lean_Meta_Sym_LitValues,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_reportIssueIfVerbose___boxed;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [114, 105, 110, 103, 32, 116, 101, 114, 109, 32, 119, 105, 116, 104, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value) as *mut leanh::LeanObject,7578295756008745317 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value) as *mut leanh::LeanObject,5779414593499529281 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value) as *mut leanh::LeanObject,7063772860359172143 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value) as *mut leanh::LeanObject,4977321555018234431 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value) as *mut leanh::LeanObject,4463466624472370110 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value) as *mut leanh::LeanObject,10422657989269798688 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value) as *mut leanh::LeanObject,16856108565602861689 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value) as *mut leanh::LeanObject,4187025665268973031 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [115, 101, 109, 105, 114, 105, 110, 103, 32, 116, 101, 114, 109, 32, 119, 105, 116, 104, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(
    mut v_inst_1270_: *mut leanh::LeanObject,
    mut v_toPure_1271_: *mut leanh::LeanObject,
    mut v_____do__lift_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: u8 = 0;
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lean_Expr_appArg_x21(v_____do__lift_1272_);
    v___x_1274_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1273_,
        v_inst_1270_,
    );
    leanh::lean_dec_ref(v___x_1273_);
    v___x_1275_ = leanh::lean_box((v___x_1274_) as usize);
    v___x_1276_ =
        leanh::lean_apply_2(v_toPure_1271_, leanh::lean_box(0), v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed(
    mut v_inst_1277_: *mut leanh::LeanObject,
    mut v_toPure_1278_: *mut leanh::LeanObject,
    mut v_____do__lift_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(
        v_inst_1277_,
        v_toPure_1278_,
        v_____do__lift_1279_,
    );
    leanh::lean_dec_ref(v_____do__lift_1279_);
    leanh::lean_dec_ref(v_inst_1277_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst___redArg(
    mut v_inst_1281_: *mut leanh::LeanObject,
    mut v_inst_1282_: *mut leanh::LeanObject,
    mut v_inst_1283_: *mut leanh::LeanObject,
    mut v_inst_1284_: *mut leanh::LeanObject,
    mut v_inst_1285_: *mut leanh::LeanObject,
    mut v_inst_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1287_ = leanh::lean_ctor_get(v_inst_1283_, 0);
    v_toBind_1288_ = leanh::lean_ctor_get(v_inst_1283_, 1);
    leanh::lean_inc(v_toBind_1288_);
    v_toPure_1289_ = leanh::lean_ctor_get(v_toApplicative_1287_, 1);
    leanh::lean_inc(v_toPure_1289_);
    v___x_1290_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(
        v_inst_1281_,
        v_inst_1282_,
        v_inst_1283_,
        v_inst_1284_,
        v_inst_1285_,
    );
    v___f_1291_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1291_, 0, v_inst_1286_);
    leanh::lean_closure_set(v___f_1291_, 1, v_toPure_1289_);
    v___x_1292_ = leanh::lean_apply_4(
        v_toBind_1288_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1290_,
        v___f_1291_,
    );
    return v___x_1292_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst(
    mut v_m_1293_: *mut leanh::LeanObject,
    mut v_inst_1294_: *mut leanh::LeanObject,
    mut v_inst_1295_: *mut leanh::LeanObject,
    mut v_inst_1296_: *mut leanh::LeanObject,
    mut v_inst_1297_: *mut leanh::LeanObject,
    mut v_inst_1298_: *mut leanh::LeanObject,
    mut v_inst_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(
        v_inst_1294_,
        v_inst_1295_,
        v_inst_1296_,
        v_inst_1297_,
        v_inst_1298_,
        v_inst_1299_,
    );
    return v___x_1300_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isMulInst___redArg(
    mut v_inst_1301_: *mut leanh::LeanObject,
    mut v_inst_1302_: *mut leanh::LeanObject,
    mut v_inst_1303_: *mut leanh::LeanObject,
    mut v_inst_1304_: *mut leanh::LeanObject,
    mut v_inst_1305_: *mut leanh::LeanObject,
    mut v_inst_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1307_ = leanh::lean_ctor_get(v_inst_1303_, 0);
    v_toBind_1308_ = leanh::lean_ctor_get(v_inst_1303_, 1);
    leanh::lean_inc(v_toBind_1308_);
    v_toPure_1309_ = leanh::lean_ctor_get(v_toApplicative_1307_, 1);
    leanh::lean_inc(v_toPure_1309_);
    v___x_1310_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(
        v_inst_1301_,
        v_inst_1302_,
        v_inst_1303_,
        v_inst_1304_,
        v_inst_1305_,
    );
    v___f_1311_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1311_, 0, v_inst_1306_);
    leanh::lean_closure_set(v___f_1311_, 1, v_toPure_1309_);
    v___x_1312_ = leanh::lean_apply_4(
        v_toBind_1308_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1310_,
        v___f_1311_,
    );
    return v___x_1312_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isMulInst(
    mut v_m_1313_: *mut leanh::LeanObject,
    mut v_inst_1314_: *mut leanh::LeanObject,
    mut v_inst_1315_: *mut leanh::LeanObject,
    mut v_inst_1316_: *mut leanh::LeanObject,
    mut v_inst_1317_: *mut leanh::LeanObject,
    mut v_inst_1318_: *mut leanh::LeanObject,
    mut v_inst_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(
        v_inst_1314_,
        v_inst_1315_,
        v_inst_1316_,
        v_inst_1317_,
        v_inst_1318_,
        v_inst_1319_,
    );
    return v___x_1320_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isSubInst___redArg(
    mut v_inst_1321_: *mut leanh::LeanObject,
    mut v_inst_1322_: *mut leanh::LeanObject,
    mut v_inst_1323_: *mut leanh::LeanObject,
    mut v_inst_1324_: *mut leanh::LeanObject,
    mut v_inst_1325_: *mut leanh::LeanObject,
    mut v_inst_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1327_ = leanh::lean_ctor_get(v_inst_1323_, 0);
    v_toBind_1328_ = leanh::lean_ctor_get(v_inst_1323_, 1);
    leanh::lean_inc(v_toBind_1328_);
    v_toPure_1329_ = leanh::lean_ctor_get(v_toApplicative_1327_, 1);
    leanh::lean_inc(v_toPure_1329_);
    v___x_1330_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(
        v_inst_1321_,
        v_inst_1322_,
        v_inst_1323_,
        v_inst_1324_,
        v_inst_1325_,
    );
    v___f_1331_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1331_, 0, v_inst_1326_);
    leanh::lean_closure_set(v___f_1331_, 1, v_toPure_1329_);
    v___x_1332_ = leanh::lean_apply_4(
        v_toBind_1328_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1330_,
        v___f_1331_,
    );
    return v___x_1332_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isSubInst(
    mut v_m_1333_: *mut leanh::LeanObject,
    mut v_inst_1334_: *mut leanh::LeanObject,
    mut v_inst_1335_: *mut leanh::LeanObject,
    mut v_inst_1336_: *mut leanh::LeanObject,
    mut v_inst_1337_: *mut leanh::LeanObject,
    mut v_inst_1338_: *mut leanh::LeanObject,
    mut v_inst_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(
        v_inst_1334_,
        v_inst_1335_,
        v_inst_1336_,
        v_inst_1337_,
        v_inst_1338_,
        v_inst_1339_,
    );
    return v___x_1340_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isNegInst___redArg(
    mut v_inst_1341_: *mut leanh::LeanObject,
    mut v_inst_1342_: *mut leanh::LeanObject,
    mut v_inst_1343_: *mut leanh::LeanObject,
    mut v_inst_1344_: *mut leanh::LeanObject,
    mut v_inst_1345_: *mut leanh::LeanObject,
    mut v_inst_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1347_ = leanh::lean_ctor_get(v_inst_1343_, 0);
    v_toBind_1348_ = leanh::lean_ctor_get(v_inst_1343_, 1);
    leanh::lean_inc(v_toBind_1348_);
    v_toPure_1349_ = leanh::lean_ctor_get(v_toApplicative_1347_, 1);
    leanh::lean_inc(v_toPure_1349_);
    v___x_1350_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(
        v_inst_1341_,
        v_inst_1342_,
        v_inst_1343_,
        v_inst_1344_,
        v_inst_1345_,
    );
    v___f_1351_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1351_, 0, v_inst_1346_);
    leanh::lean_closure_set(v___f_1351_, 1, v_toPure_1349_);
    v___x_1352_ = leanh::lean_apply_4(
        v_toBind_1348_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1350_,
        v___f_1351_,
    );
    return v___x_1352_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isNegInst(
    mut v_m_1353_: *mut leanh::LeanObject,
    mut v_inst_1354_: *mut leanh::LeanObject,
    mut v_inst_1355_: *mut leanh::LeanObject,
    mut v_inst_1356_: *mut leanh::LeanObject,
    mut v_inst_1357_: *mut leanh::LeanObject,
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_inst_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(
        v_inst_1354_,
        v_inst_1355_,
        v_inst_1356_,
        v_inst_1357_,
        v_inst_1358_,
        v_inst_1359_,
    );
    return v___x_1360_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isPowInst___redArg(
    mut v_inst_1361_: *mut leanh::LeanObject,
    mut v_inst_1362_: *mut leanh::LeanObject,
    mut v_inst_1363_: *mut leanh::LeanObject,
    mut v_inst_1364_: *mut leanh::LeanObject,
    mut v_inst_1365_: *mut leanh::LeanObject,
    mut v_inst_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1367_ = leanh::lean_ctor_get(v_inst_1363_, 0);
    v_toBind_1368_ = leanh::lean_ctor_get(v_inst_1363_, 1);
    leanh::lean_inc(v_toBind_1368_);
    v_toPure_1369_ = leanh::lean_ctor_get(v_toApplicative_1367_, 1);
    leanh::lean_inc(v_toPure_1369_);
    v___x_1370_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(
        v_inst_1361_,
        v_inst_1362_,
        v_inst_1363_,
        v_inst_1364_,
        v_inst_1365_,
    );
    v___f_1371_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1371_, 0, v_inst_1366_);
    leanh::lean_closure_set(v___f_1371_, 1, v_toPure_1369_);
    v___x_1372_ = leanh::lean_apply_4(
        v_toBind_1368_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1370_,
        v___f_1371_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isPowInst(
    mut v_m_1373_: *mut leanh::LeanObject,
    mut v_inst_1374_: *mut leanh::LeanObject,
    mut v_inst_1375_: *mut leanh::LeanObject,
    mut v_inst_1376_: *mut leanh::LeanObject,
    mut v_inst_1377_: *mut leanh::LeanObject,
    mut v_inst_1378_: *mut leanh::LeanObject,
    mut v_inst_1379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(
        v_inst_1374_,
        v_inst_1375_,
        v_inst_1376_,
        v_inst_1377_,
        v_inst_1378_,
        v_inst_1379_,
    );
    return v___x_1380_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(
    mut v_inst_1381_: *mut leanh::LeanObject,
    mut v_inst_1382_: *mut leanh::LeanObject,
    mut v_inst_1383_: *mut leanh::LeanObject,
    mut v_inst_1384_: *mut leanh::LeanObject,
    mut v_inst_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1386_ = leanh::lean_ctor_get(v_inst_1382_, 0);
    v_toBind_1387_ = leanh::lean_ctor_get(v_inst_1382_, 1);
    leanh::lean_inc(v_toBind_1387_);
    v_toPure_1388_ = leanh::lean_ctor_get(v_toApplicative_1386_, 1);
    leanh::lean_inc(v_toPure_1388_);
    v___x_1389_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(
        v_inst_1381_,
        v_inst_1382_,
        v_inst_1383_,
        v_inst_1384_,
    );
    v___f_1390_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1390_, 0, v_inst_1385_);
    leanh::lean_closure_set(v___f_1390_, 1, v_toPure_1388_);
    v___x_1391_ = leanh::lean_apply_4(
        v_toBind_1387_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1389_,
        v___f_1390_,
    );
    return v___x_1391_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isIntCastInst(
    mut v_m_1392_: *mut leanh::LeanObject,
    mut v_inst_1393_: *mut leanh::LeanObject,
    mut v_inst_1394_: *mut leanh::LeanObject,
    mut v_inst_1395_: *mut leanh::LeanObject,
    mut v_inst_1396_: *mut leanh::LeanObject,
    mut v_inst_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(
        v_inst_1393_,
        v_inst_1394_,
        v_inst_1395_,
        v_inst_1396_,
        v_inst_1397_,
    );
    return v___x_1398_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(
    mut v_inst_1399_: *mut leanh::LeanObject,
    mut v_inst_1400_: *mut leanh::LeanObject,
    mut v_inst_1401_: *mut leanh::LeanObject,
    mut v_inst_1402_: *mut leanh::LeanObject,
    mut v_inst_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1404_ = leanh::lean_ctor_get(v_inst_1400_, 0);
    v_toBind_1405_ = leanh::lean_ctor_get(v_inst_1400_, 1);
    leanh::lean_inc(v_toBind_1405_);
    v_toPure_1406_ = leanh::lean_ctor_get(v_toApplicative_1404_, 1);
    leanh::lean_inc(v_toPure_1406_);
    v___x_1407_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
        v_inst_1399_,
        v_inst_1400_,
        v_inst_1401_,
        v_inst_1402_,
    );
    v___f_1408_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1408_, 0, v_inst_1403_);
    leanh::lean_closure_set(v___f_1408_, 1, v_toPure_1406_);
    v___x_1409_ = leanh::lean_apply_4(
        v_toBind_1405_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1407_,
        v___f_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isNatCastInst(
    mut v_m_1410_: *mut leanh::LeanObject,
    mut v_inst_1411_: *mut leanh::LeanObject,
    mut v_inst_1412_: *mut leanh::LeanObject,
    mut v_inst_1413_: *mut leanh::LeanObject,
    mut v_inst_1414_: *mut leanh::LeanObject,
    mut v_inst_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(
        v_inst_1411_,
        v_inst_1412_,
        v_inst_1413_,
        v_inst_1414_,
        v_inst_1415_,
    );
    return v___x_1416_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1418_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0;
    v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
    mut v_inst_1420_: *mut leanh::LeanObject,
    mut v_e_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1);
    v___x_1423_ = l_Lean_indentExpr(v_e_1421_);
    v___x_1424_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1424_, 0, v___x_1422_);
    leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
    v___x_1425_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_reportIssueIfVerbose___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    leanh::lean_closure_set(v___x_1425_, 0, v___x_1424_);
    v___x_1426_ = leanh::lean_apply_2(v_inst_1420_, leanh::lean_box(0), v___x_1425_);
    return v___x_1426_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue(
    mut v_m_1427_: *mut leanh::LeanObject,
    mut v_inst_1428_: *mut leanh::LeanObject,
    mut v_e_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
            v_inst_1428_,
            v_e_1429_,
        );
    return v___x_1430_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0(
    mut v_toPure_1431_: *mut leanh::LeanObject,
    mut v_____do__lift_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1433_, 0, v_____do__lift_1432_);
    v___x_1434_ =
        leanh::lean_apply_2(v_toPure_1431_, leanh::lean_box(0), v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1(
    mut v_____do__lift_1435_: *mut leanh::LeanObject,
    mut v_toPure_1436_: *mut leanh::LeanObject,
    mut v_____do__lift_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1438_, 0, v_____do__lift_1435_);
    leanh::lean_ctor_set(v___x_1438_, 1, v_____do__lift_1437_);
    v___x_1439_ =
        leanh::lean_apply_2(v_toPure_1436_, leanh::lean_box(0), v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(
    mut v_asVar_1440_: *mut leanh::LeanObject,
    mut v_e_1441_: *mut leanh::LeanObject,
    mut v_arg_1442_: *mut leanh::LeanObject,
    mut v_toPure_1443_: *mut leanh::LeanObject,
    mut v_toVar_1444_: *mut leanh::LeanObject,
    mut v_____do__lift_1445_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1445_ == 0 {
                    leanh::lean_dec(v_toVar_1444_);
                    leanh::lean_dec(v_toPure_1443_);
                    leanh::lean_dec_ref(v_arg_1442_);
                    v___x_1446_ = leanh::lean_apply_1(v_asVar_1440_, v_e_1441_);
                    return v___x_1446_;
                } else {
                    leanh::lean_dec(v_asVar_1440_);
                    v___x_1447_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_1442_);
                    if leanh::lean_obj_tag(v___x_1447_) == 1 {
                        leanh::lean_dec(v_toVar_1444_);
                        leanh::lean_dec_ref(v_e_1441_);
                        v_val_1448_ = leanh::lean_ctor_get(v___x_1447_, 0);
                        v_isSharedCheck_1456_ =
                            (!leanh::lean_is_exclusive(v___x_1447_)) as u8;
                        if v_isSharedCheck_1456_ == 0 {
                            v___x_1450_ = v___x_1447_;
                            v_isShared_1451_ = v_isSharedCheck_1456_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1448_);
                            leanh::lean_dec(v___x_1447_);
                            v___x_1450_ = leanh::lean_box(0);
                            v_isShared_1451_ = v_isSharedCheck_1456_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1447_);
                        leanh::lean_dec(v_toPure_1443_);
                        v___x_1457_ = leanh::lean_apply_1(v_toVar_1444_, v_e_1441_);
                        return v___x_1457_;
                    }
                }
            }
            1 => {
                if v_isShared_1451_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1450_, 2);
                    v___x_1453_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1448_);
                    v___x_1453_ = v_reuseFailAlloc_1455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1454_ = leanh::lean_apply_2(
                    v_toPure_1443_,
                    leanh::lean_box(0),
                    v___x_1453_,
                );
                return v___x_1454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed(
    mut v_asVar_1458_: *mut leanh::LeanObject,
    mut v_e_1459_: *mut leanh::LeanObject,
    mut v_arg_1460_: *mut leanh::LeanObject,
    mut v_toPure_1461_: *mut leanh::LeanObject,
    mut v_toVar_1462_: *mut leanh::LeanObject,
    mut v_____do__lift_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_4904__boxed_1464_: u8 = 0;
    let mut v_res_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4904__boxed_1464_ = (leanh::lean_unbox(v_____do__lift_1463_) as u8);
    v_res_1465_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_1458_, v_e_1459_, v_arg_1460_, v_toPure_1461_, v_toVar_1462_, v_____do__lift_4904__boxed_1464_);
    return v_res_1465_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7(
    mut v_____do__lift_1466_: *mut leanh::LeanObject,
    mut v_toPure_1467_: *mut leanh::LeanObject,
    mut v_____do__lift_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1469_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1469_, 0, v_____do__lift_1466_);
    leanh::lean_ctor_set(v___x_1469_, 1, v_____do__lift_1468_);
    v___x_1470_ =
        leanh::lean_apply_2(v_toPure_1467_, leanh::lean_box(0), v___x_1469_);
    return v___x_1470_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4(
    mut v_____do__lift_1471_: *mut leanh::LeanObject,
    mut v_toPure_1472_: *mut leanh::LeanObject,
    mut v_____do__lift_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1474_, 0, v_____do__lift_1471_);
    leanh::lean_ctor_set(v___x_1474_, 1, v_____do__lift_1473_);
    v___x_1475_ =
        leanh::lean_apply_2(v_toPure_1472_, leanh::lean_box(0), v___x_1474_);
    return v___x_1475_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9(
    mut v_val_1476_: *mut leanh::LeanObject,
    mut v_toPure_1477_: *mut leanh::LeanObject,
    mut v_____do__lift_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1479_, 0, v_____do__lift_1478_);
    leanh::lean_ctor_set(v___x_1479_, 1, v_val_1476_);
    v___x_1480_ =
        leanh::lean_apply_2(v_toPure_1477_, leanh::lean_box(0), v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(
    mut v_asVar_1481_: *mut leanh::LeanObject,
    mut v_e_1482_: *mut leanh::LeanObject,
    mut v_arg_1483_: *mut leanh::LeanObject,
    mut v_toPure_1484_: *mut leanh::LeanObject,
    mut v_toVar_1485_: *mut leanh::LeanObject,
    mut v_____do__lift_1486_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1486_ == 0 {
                    leanh::lean_dec(v_toVar_1485_);
                    leanh::lean_dec(v_toPure_1484_);
                    leanh::lean_dec_ref(v_arg_1483_);
                    v___x_1487_ = leanh::lean_apply_1(v_asVar_1481_, v_e_1482_);
                    return v___x_1487_;
                } else {
                    leanh::lean_dec(v_asVar_1481_);
                    v___x_1488_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1483_);
                    if leanh::lean_obj_tag(v___x_1488_) == 1 {
                        leanh::lean_dec(v_toVar_1485_);
                        leanh::lean_dec_ref(v_e_1482_);
                        v_val_1489_ = leanh::lean_ctor_get(v___x_1488_, 0);
                        v_isSharedCheck_1497_ =
                            (!leanh::lean_is_exclusive(v___x_1488_)) as u8;
                        if v_isSharedCheck_1497_ == 0 {
                            v___x_1491_ = v___x_1488_;
                            v_isShared_1492_ = v_isSharedCheck_1497_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1489_);
                            leanh::lean_dec(v___x_1488_);
                            v___x_1491_ = leanh::lean_box(0);
                            v_isShared_1492_ = v_isSharedCheck_1497_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1488_);
                        leanh::lean_dec(v_toPure_1484_);
                        v___x_1498_ = leanh::lean_apply_1(v_toVar_1485_, v_e_1482_);
                        return v___x_1498_;
                    }
                }
            }
            1 => {
                if v_isShared_1492_ == 0 {
                    v___x_1494_ = v___x_1491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_val_1489_);
                    v___x_1494_ = v_reuseFailAlloc_1496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1495_ = leanh::lean_apply_2(
                    v_toPure_1484_,
                    leanh::lean_box(0),
                    v___x_1494_,
                );
                return v___x_1495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed(
    mut v_asVar_1499_: *mut leanh::LeanObject,
    mut v_e_1500_: *mut leanh::LeanObject,
    mut v_arg_1501_: *mut leanh::LeanObject,
    mut v_toPure_1502_: *mut leanh::LeanObject,
    mut v_toVar_1503_: *mut leanh::LeanObject,
    mut v_____do__lift_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_4958__boxed_1505_: u8 = 0;
    let mut v_res_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4958__boxed_1505_ = (leanh::lean_unbox(v_____do__lift_1504_) as u8);
    v_res_1506_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_1499_, v_e_1500_, v_arg_1501_, v_toPure_1502_, v_toVar_1503_, v_____do__lift_4958__boxed_1505_);
    return v_res_1506_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(
    mut v_asVar_1551_: *mut leanh::LeanObject,
    mut v_e_1552_: *mut leanh::LeanObject,
    mut v_inst_1553_: *mut leanh::LeanObject,
    mut v_inst_1554_: *mut leanh::LeanObject,
    mut v_inst_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
    mut v_inst_1557_: *mut leanh::LeanObject,
    mut v_toVar_1558_: *mut leanh::LeanObject,
    mut v_arg_1559_: *mut leanh::LeanObject,
    mut v_toBind_1560_: *mut leanh::LeanObject,
    mut v___f_1561_: *mut leanh::LeanObject,
    mut v_____do__lift_1562_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1562_ == 0 {
        let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_1561_);
        leanh::lean_dec(v_toBind_1560_);
        leanh::lean_dec_ref(v_arg_1559_);
        leanh::lean_dec(v_toVar_1558_);
        leanh::lean_dec_ref(v_inst_1557_);
        leanh::lean_dec_ref(v_inst_1556_);
        leanh::lean_dec_ref(v_inst_1555_);
        leanh::lean_dec_ref(v_inst_1554_);
        leanh::lean_dec(v_inst_1553_);
        v___x_1563_ = leanh::lean_apply_1(v_asVar_1551_, v_e_1552_);
        return v___x_1563_;
    } else {
        let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_1552_);
        v___x_1564_ =
            l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
                v_inst_1553_,
                v_inst_1554_,
                v_inst_1555_,
                v_inst_1556_,
                v_inst_1557_,
                v_toVar_1558_,
                v_asVar_1551_,
                v_arg_1559_,
            );
        v___x_1565_ = leanh::lean_apply_4(
            v_toBind_1560_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1564_,
            v___f_1561_,
        );
        return v___x_1565_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed(
    mut v_asVar_1566_: *mut leanh::LeanObject,
    mut v_e_1567_: *mut leanh::LeanObject,
    mut v_inst_1568_: *mut leanh::LeanObject,
    mut v_inst_1569_: *mut leanh::LeanObject,
    mut v_inst_1570_: *mut leanh::LeanObject,
    mut v_inst_1571_: *mut leanh::LeanObject,
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_toVar_1573_: *mut leanh::LeanObject,
    mut v_arg_1574_: *mut leanh::LeanObject,
    mut v_toBind_1575_: *mut leanh::LeanObject,
    mut v___f_1576_: *mut leanh::LeanObject,
    mut v_____do__lift_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_5068__boxed_1578_: u8 = 0;
    let mut v_res_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_5068__boxed_1578_ = (leanh::lean_unbox(v_____do__lift_1577_) as u8);
    v_res_1579_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_1566_, v_e_1567_, v_inst_1568_, v_inst_1569_, v_inst_1570_, v_inst_1571_, v_inst_1572_, v_toVar_1573_, v_arg_1574_, v_toBind_1575_, v___f_1576_, v_____do__lift_5068__boxed_1578_);
    return v_res_1579_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5(
    mut v_toPure_1580_: *mut leanh::LeanObject,
    mut v_inst_1581_: *mut leanh::LeanObject,
    mut v_inst_1582_: *mut leanh::LeanObject,
    mut v_inst_1583_: *mut leanh::LeanObject,
    mut v_inst_1584_: *mut leanh::LeanObject,
    mut v_inst_1585_: *mut leanh::LeanObject,
    mut v_toVar_1586_: *mut leanh::LeanObject,
    mut v_asVar_1587_: *mut leanh::LeanObject,
    mut v_arg_1588_: *mut leanh::LeanObject,
    mut v_toBind_1589_: *mut leanh::LeanObject,
    mut v_____do__lift_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1591_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_1591_, 0, v_____do__lift_1590_);
    leanh::lean_closure_set(v___f_1591_, 1, v_toPure_1580_);
    v___x_1592_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1581_,
            v_inst_1582_,
            v_inst_1583_,
            v_inst_1584_,
            v_inst_1585_,
            v_toVar_1586_,
            v_asVar_1587_,
            v_arg_1588_,
        );
    v___x_1593_ = leanh::lean_apply_4(
        v_toBind_1589_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1592_,
        v___f_1591_,
    );
    return v___x_1593_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6(
    mut v_toPure_1594_: *mut leanh::LeanObject,
    mut v_inst_1595_: *mut leanh::LeanObject,
    mut v_inst_1596_: *mut leanh::LeanObject,
    mut v_inst_1597_: *mut leanh::LeanObject,
    mut v_inst_1598_: *mut leanh::LeanObject,
    mut v_inst_1599_: *mut leanh::LeanObject,
    mut v_toVar_1600_: *mut leanh::LeanObject,
    mut v_asVar_1601_: *mut leanh::LeanObject,
    mut v_arg_1602_: *mut leanh::LeanObject,
    mut v_toBind_1603_: *mut leanh::LeanObject,
    mut v_____do__lift_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1605_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_1605_, 0, v_____do__lift_1604_);
    leanh::lean_closure_set(v___f_1605_, 1, v_toPure_1594_);
    v___x_1606_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1595_,
            v_inst_1596_,
            v_inst_1597_,
            v_inst_1598_,
            v_inst_1599_,
            v_toVar_1600_,
            v_asVar_1601_,
            v_arg_1602_,
        );
    v___x_1607_ = leanh::lean_apply_4(
        v_toBind_1603_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1606_,
        v___f_1605_,
    );
    return v___x_1607_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(
    mut v_toVar_1608_: *mut leanh::LeanObject,
    mut v_e_1609_: *mut leanh::LeanObject,
    mut v_toPure_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
    mut v_inst_1612_: *mut leanh::LeanObject,
    mut v_inst_1613_: *mut leanh::LeanObject,
    mut v_inst_1614_: *mut leanh::LeanObject,
    mut v_inst_1615_: *mut leanh::LeanObject,
    mut v_asVar_1616_: *mut leanh::LeanObject,
    mut v_toBind_1617_: *mut leanh::LeanObject,
    mut v___f_1618_: *mut leanh::LeanObject,
    mut v_____x_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1635_ = l_Lean_Expr_cleanupAnnotations(v_____x_1619_);
                v___x_1636_ = l_Lean_Expr_isApp(v___x_1635_);
                if v___x_1636_ == 0 {
                    leanh::lean_dec_ref(v___x_1635_);
                    leanh::lean_dec(v___f_1618_);
                    leanh::lean_dec(v_toBind_1617_);
                    leanh::lean_dec(v_asVar_1616_);
                    leanh::lean_dec_ref(v_inst_1615_);
                    leanh::lean_dec_ref(v_inst_1614_);
                    leanh::lean_dec_ref(v_inst_1613_);
                    leanh::lean_dec_ref(v_inst_1612_);
                    leanh::lean_dec(v_inst_1611_);
                    leanh::lean_dec(v_toPure_1610_);
                    v___x_1637_ = leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                    return v___x_1637_;
                } else {
                    v_arg_1638_ = leanh::lean_ctor_get(v___x_1635_, 1);
                    leanh::lean_inc_ref(v_arg_1638_);
                    v___x_1639_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1635_);
                    v___x_1640_ = l_Lean_Expr_isApp(v___x_1639_);
                    if v___x_1640_ == 0 {
                        leanh::lean_dec_ref(v___x_1639_);
                        leanh::lean_dec_ref(v_arg_1638_);
                        leanh::lean_dec(v___f_1618_);
                        leanh::lean_dec(v_toBind_1617_);
                        leanh::lean_dec(v_asVar_1616_);
                        leanh::lean_dec_ref(v_inst_1615_);
                        leanh::lean_dec_ref(v_inst_1614_);
                        leanh::lean_dec_ref(v_inst_1613_);
                        leanh::lean_dec_ref(v_inst_1612_);
                        leanh::lean_dec(v_inst_1611_);
                        leanh::lean_dec(v_toPure_1610_);
                        v___x_1641_ = leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                        return v___x_1641_;
                    } else {
                        v_arg_1642_ = leanh::lean_ctor_get(v___x_1639_, 1);
                        leanh::lean_inc_ref(v_arg_1642_);
                        v___x_1643_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1639_);
                        v___x_1644_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2;
                        v___x_1645_ = l_Lean_Expr_isConstOf(v___x_1643_, v___x_1644_);
                        if v___x_1645_ == 0 {
                            v___x_1646_ = l_Lean_Expr_isApp(v___x_1643_);
                            if v___x_1646_ == 0 {
                                leanh::lean_dec_ref(v___x_1643_);
                                leanh::lean_dec_ref(v_arg_1642_);
                                leanh::lean_dec_ref(v_arg_1638_);
                                leanh::lean_dec(v___f_1618_);
                                leanh::lean_dec(v_toBind_1617_);
                                leanh::lean_dec(v_asVar_1616_);
                                leanh::lean_dec_ref(v_inst_1615_);
                                leanh::lean_dec_ref(v_inst_1614_);
                                leanh::lean_dec_ref(v_inst_1613_);
                                leanh::lean_dec_ref(v_inst_1612_);
                                leanh::lean_dec(v_inst_1611_);
                                leanh::lean_dec(v_toPure_1610_);
                                v___x_1647_ = leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                                return v___x_1647_;
                            } else {
                                v_arg_1648_ = leanh::lean_ctor_get(v___x_1643_, 1);
                                leanh::lean_inc_ref(v_arg_1648_);
                                v___x_1649_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1643_);
                                v___x_1650_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4;
                                v___x_1651_ = l_Lean_Expr_isConstOf(v___x_1649_, v___x_1650_);
                                if v___x_1651_ == 0 {
                                    v___x_1652_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7;
                                    v___x_1653_ = l_Lean_Expr_isConstOf(v___x_1649_, v___x_1652_);
                                    if v___x_1653_ == 0 {
                                        v___x_1654_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10;
                                        v___x_1655_ =
                                            l_Lean_Expr_isConstOf(v___x_1649_, v___x_1654_);
                                        if v___x_1655_ == 0 {
                                            v___x_1656_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13;
                                            v___x_1657_ =
                                                l_Lean_Expr_isConstOf(v___x_1649_, v___x_1656_);
                                            if v___x_1657_ == 0 {
                                                leanh::lean_dec(v___f_1618_);
                                                v___x_1658_ = l_Lean_Expr_isApp(v___x_1649_);
                                                if v___x_1658_ == 0 {
                                                    leanh::lean_dec_ref(v___x_1649_);
                                                    leanh::lean_dec_ref(v_arg_1648_);
                                                    leanh::lean_dec_ref(v_arg_1642_);
                                                    leanh::lean_dec_ref(v_arg_1638_);
                                                    leanh::lean_dec(v_toBind_1617_);
                                                    leanh::lean_dec(v_asVar_1616_);
                                                    leanh::lean_dec_ref(v_inst_1615_);
                                                    leanh::lean_dec_ref(v_inst_1614_);
                                                    leanh::lean_dec_ref(v_inst_1613_);
                                                    leanh::lean_dec_ref(v_inst_1612_);
                                                    leanh::lean_dec(v_inst_1611_);
                                                    leanh::lean_dec(v_toPure_1610_);
                                                    v___x_1659_ = leanh::lean_apply_1(
                                                        v_toVar_1608_,
                                                        v_e_1609_,
                                                    );
                                                    return v___x_1659_;
                                                } else {
                                                    v___x_1660_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1649_,
                                                    );
                                                    v___x_1661_ = l_Lean_Expr_isApp(v___x_1660_);
                                                    if v___x_1661_ == 0 {
                                                        leanh::lean_dec_ref(v___x_1660_);
                                                        leanh::lean_dec_ref(v_arg_1648_);
                                                        leanh::lean_dec_ref(v_arg_1642_);
                                                        leanh::lean_dec_ref(v_arg_1638_);
                                                        leanh::lean_dec(v_toBind_1617_);
                                                        leanh::lean_dec(v_asVar_1616_);
                                                        leanh::lean_dec_ref(v_inst_1615_);
                                                        leanh::lean_dec_ref(v_inst_1614_);
                                                        leanh::lean_dec_ref(v_inst_1613_);
                                                        leanh::lean_dec_ref(v_inst_1612_);
                                                        leanh::lean_dec(v_inst_1611_);
                                                        leanh::lean_dec(v_toPure_1610_);
                                                        v___x_1662_ = leanh::lean_apply_1(
                                                            v_toVar_1608_,
                                                            v_e_1609_,
                                                        );
                                                        return v___x_1662_;
                                                    } else {
                                                        v___x_1663_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1660_,
                                                            );
                                                        v___x_1664_ =
                                                            l_Lean_Expr_isApp(v___x_1663_);
                                                        if v___x_1664_ == 0 {
                                                            leanh::lean_dec_ref(v___x_1663_);
                                                            leanh::lean_dec_ref(v_arg_1648_);
                                                            leanh::lean_dec_ref(v_arg_1642_);
                                                            leanh::lean_dec_ref(v_arg_1638_);
                                                            leanh::lean_dec(v_toBind_1617_);
                                                            leanh::lean_dec(v_asVar_1616_);
                                                            leanh::lean_dec_ref(
                                                                v_inst_1615_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_1614_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_1613_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_1612_,
                                                            );
                                                            leanh::lean_dec(v_inst_1611_);
                                                            leanh::lean_dec(v_toPure_1610_);
                                                            v___x_1665_ =
                                                                leanh::lean_apply_1(
                                                                    v_toVar_1608_,
                                                                    v_e_1609_,
                                                                );
                                                            return v___x_1665_;
                                                        } else {
                                                            v___x_1666_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_1663_,
                                                                );
                                                            v___x_1667_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16;
                                                            v___x_1668_ = l_Lean_Expr_isConstOf(
                                                                v___x_1666_,
                                                                v___x_1667_,
                                                            );
                                                            if v___x_1668_ == 0 {
                                                                v___x_1669_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19;
                                                                v___x_1670_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1666_,
                                                                    v___x_1669_,
                                                                );
                                                                if v___x_1670_ == 0 {
                                                                    v___x_1671_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22;
                                                                    v___x_1672_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1666_,
                                                                            v___x_1671_,
                                                                        );
                                                                    if v___x_1672_ == 0 {
                                                                        v___x_1673_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25;
                                                                        v___x_1674_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_1666_,
                                                                                v___x_1673_,
                                                                            );
                                                                        leanh::lean_dec_ref(
                                                                            v___x_1666_,
                                                                        );
                                                                        if v___x_1674_ == 0 {
                                                                            leanh::lean_dec_ref(v_arg_1648_);
                                                                            leanh::lean_dec_ref(v_arg_1642_);
                                                                            leanh::lean_dec_ref(v_arg_1638_);
                                                                            leanh::lean_dec(
                                                                                v_toBind_1617_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v_asVar_1616_,
                                                                            );
                                                                            leanh::lean_dec_ref(v_inst_1615_);
                                                                            leanh::lean_dec_ref(v_inst_1614_);
                                                                            leanh::lean_dec_ref(v_inst_1613_);
                                                                            leanh::lean_dec_ref(v_inst_1612_);
                                                                            leanh::lean_dec(
                                                                                v_inst_1611_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v_toPure_1610_,
                                                                            );
                                                                            v___x_1675_ = leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                                                                            return v___x_1675_;
                                                                        } else {
                                                                            leanh::lean_inc_n(v_toBind_1617_, 2);
                                                                            leanh::lean_inc(
                                                                                v_asVar_1616_,
                                                                            );
                                                                            leanh::lean_inc(
                                                                                v_toVar_1608_,
                                                                            );
                                                                            leanh::lean_inc_ref_n(v_inst_1615_, 2);
                                                                            leanh::lean_inc_ref_n(v_inst_1614_, 2);
                                                                            leanh::lean_inc_ref_n(v_inst_1613_, 2);
                                                                            leanh::lean_inc_ref_n(v_inst_1612_, 2);
                                                                            leanh::lean_inc_n(v_inst_1611_, 2);
                                                                            v___f_1676_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2 as *mut core::ffi::c_void, 11, 10);
                                                                            leanh::lean_closure_set(v___f_1676_, 0, v_toPure_1610_);
                                                                            leanh::lean_closure_set(v___f_1676_, 1, v_inst_1611_);
                                                                            leanh::lean_closure_set(v___f_1676_, 2, v_inst_1612_);
                                                                            leanh::lean_closure_set(v___f_1676_, 3, v_inst_1613_);
                                                                            leanh::lean_closure_set(v___f_1676_, 4, v_inst_1614_);
                                                                            leanh::lean_closure_set(v___f_1676_, 5, v_inst_1615_);
                                                                            leanh::lean_closure_set(v___f_1676_, 6, v_toVar_1608_);
                                                                            leanh::lean_closure_set(v___f_1676_, 7, v_asVar_1616_);
                                                                            leanh::lean_closure_set(v___f_1676_, 8, v_arg_1638_);
                                                                            leanh::lean_closure_set(v___f_1676_, 9, v_toBind_1617_);
                                                                            v___f_1677_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                            leanh::lean_closure_set(v___f_1677_, 0, v_asVar_1616_);
                                                                            leanh::lean_closure_set(v___f_1677_, 1, v_e_1609_);
                                                                            leanh::lean_closure_set(v___f_1677_, 2, v_inst_1611_);
                                                                            leanh::lean_closure_set(v___f_1677_, 3, v_inst_1612_);
                                                                            leanh::lean_closure_set(v___f_1677_, 4, v_inst_1613_);
                                                                            leanh::lean_closure_set(v___f_1677_, 5, v_inst_1614_);
                                                                            leanh::lean_closure_set(v___f_1677_, 6, v_inst_1615_);
                                                                            leanh::lean_closure_set(v___f_1677_, 7, v_toVar_1608_);
                                                                            leanh::lean_closure_set(v___f_1677_, 8, v_arg_1642_);
                                                                            leanh::lean_closure_set(v___f_1677_, 9, v_toBind_1617_);
                                                                            leanh::lean_closure_set(v___f_1677_, 10, v___f_1676_);
                                                                            v___x_1678_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                            v___x_1679_ = leanh::lean_apply_4(v_toBind_1617_, leanh::lean_box(0), leanh::lean_box(0), v___x_1678_, v___f_1677_);
                                                                            return v___x_1679_;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_1666_,
                                                                        );
                                                                        leanh::lean_inc_n(
                                                                            v_toBind_1617_,
                                                                            2,
                                                                        );
                                                                        leanh::lean_inc(
                                                                            v_asVar_1616_,
                                                                        );
                                                                        leanh::lean_inc(
                                                                            v_toVar_1608_,
                                                                        );
                                                                        leanh::lean_inc_ref_n(v_inst_1615_, 2);
                                                                        leanh::lean_inc_ref_n(v_inst_1614_, 2);
                                                                        leanh::lean_inc_ref_n(v_inst_1613_, 2);
                                                                        leanh::lean_inc_ref_n(v_inst_1612_, 2);
                                                                        leanh::lean_inc_n(
                                                                            v_inst_1611_,
                                                                            2,
                                                                        );
                                                                        v___f_1680_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5 as *mut core::ffi::c_void, 11, 10);
                                                                        leanh::lean_closure_set(v___f_1680_, 0, v_toPure_1610_);
                                                                        leanh::lean_closure_set(v___f_1680_, 1, v_inst_1611_);
                                                                        leanh::lean_closure_set(v___f_1680_, 2, v_inst_1612_);
                                                                        leanh::lean_closure_set(v___f_1680_, 3, v_inst_1613_);
                                                                        leanh::lean_closure_set(v___f_1680_, 4, v_inst_1614_);
                                                                        leanh::lean_closure_set(v___f_1680_, 5, v_inst_1615_);
                                                                        leanh::lean_closure_set(v___f_1680_, 6, v_toVar_1608_);
                                                                        leanh::lean_closure_set(v___f_1680_, 7, v_asVar_1616_);
                                                                        leanh::lean_closure_set(v___f_1680_, 8, v_arg_1638_);
                                                                        leanh::lean_closure_set(v___f_1680_, 9, v_toBind_1617_);
                                                                        v___f_1681_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                        leanh::lean_closure_set(v___f_1681_, 0, v_asVar_1616_);
                                                                        leanh::lean_closure_set(v___f_1681_, 1, v_e_1609_);
                                                                        leanh::lean_closure_set(v___f_1681_, 2, v_inst_1611_);
                                                                        leanh::lean_closure_set(v___f_1681_, 3, v_inst_1612_);
                                                                        leanh::lean_closure_set(v___f_1681_, 4, v_inst_1613_);
                                                                        leanh::lean_closure_set(v___f_1681_, 5, v_inst_1614_);
                                                                        leanh::lean_closure_set(v___f_1681_, 6, v_inst_1615_);
                                                                        leanh::lean_closure_set(v___f_1681_, 7, v_toVar_1608_);
                                                                        leanh::lean_closure_set(v___f_1681_, 8, v_arg_1642_);
                                                                        leanh::lean_closure_set(v___f_1681_, 9, v_toBind_1617_);
                                                                        leanh::lean_closure_set(v___f_1681_, 10, v___f_1680_);
                                                                        v___x_1682_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                        v___x_1683_ = leanh::lean_apply_4(v_toBind_1617_, leanh::lean_box(0), leanh::lean_box(0), v___x_1682_, v___f_1681_);
                                                                        return v___x_1683_;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_1666_,
                                                                    );
                                                                    leanh::lean_inc_n(
                                                                        v_toBind_1617_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_asVar_1616_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_toVar_1608_,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1615_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1614_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1613_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1612_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_n(
                                                                        v_inst_1611_,
                                                                        2,
                                                                    );
                                                                    v___f_1684_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        0,
                                                                        v_toPure_1610_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        1,
                                                                        v_inst_1611_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        2,
                                                                        v_inst_1612_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        3,
                                                                        v_inst_1613_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        4,
                                                                        v_inst_1614_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        5,
                                                                        v_inst_1615_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        6,
                                                                        v_toVar_1608_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        7,
                                                                        v_asVar_1616_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        8,
                                                                        v_arg_1638_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        9,
                                                                        v_toBind_1617_,
                                                                    );
                                                                    v___f_1685_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        0,
                                                                        v_asVar_1616_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        1,
                                                                        v_e_1609_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        2,
                                                                        v_inst_1611_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        3,
                                                                        v_inst_1612_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        4,
                                                                        v_inst_1613_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        5,
                                                                        v_inst_1614_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        6,
                                                                        v_inst_1615_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        7,
                                                                        v_toVar_1608_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        8,
                                                                        v_arg_1642_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        9,
                                                                        v_toBind_1617_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        10,
                                                                        v___f_1684_,
                                                                    );
                                                                    v___x_1686_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                    v___x_1687_ =
                                                                        leanh::lean_apply_4(
                                                                            v_toBind_1617_,
                                                                            leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            v___x_1686_,
                                                                            v___f_1685_,
                                                                        );
                                                                    return v___x_1687_;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_1666_,
                                                                );
                                                                v___x_1688_ =
                                                                    l_Lean_Meta_Sym_getNatValue_x3f(
                                                                        v_arg_1638_,
                                                                    );
                                                                if leanh::lean_obj_tag(
                                                                    v___x_1688_,
                                                                ) == 1
                                                                {
                                                                    v_val_1689_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_1688_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_val_1689_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v___x_1688_, 1);
                                                                    v___f_1690_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9 as *mut core::ffi::c_void, 3, 2);
                                                                    leanh::lean_closure_set(
                                                                        v___f_1690_,
                                                                        0,
                                                                        v_val_1689_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1690_,
                                                                        1,
                                                                        v_toPure_1610_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_toBind_1617_,
                                                                    );
                                                                    leanh::lean_inc_ref(
                                                                        v_inst_1615_,
                                                                    );
                                                                    leanh::lean_inc_ref(
                                                                        v_inst_1614_,
                                                                    );
                                                                    leanh::lean_inc_ref(
                                                                        v_inst_1613_,
                                                                    );
                                                                    leanh::lean_inc_ref(
                                                                        v_inst_1612_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_inst_1611_,
                                                                    );
                                                                    v___f_1691_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        0,
                                                                        v_asVar_1616_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        1,
                                                                        v_e_1609_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        2,
                                                                        v_inst_1611_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        3,
                                                                        v_inst_1612_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        4,
                                                                        v_inst_1613_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        5,
                                                                        v_inst_1614_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        6,
                                                                        v_inst_1615_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        7,
                                                                        v_toVar_1608_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        8,
                                                                        v_arg_1642_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        9,
                                                                        v_toBind_1617_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        10,
                                                                        v___f_1690_,
                                                                    );
                                                                    v___x_1692_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                    v___x_1693_ =
                                                                        leanh::lean_apply_4(
                                                                            v_toBind_1617_,
                                                                            leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            v___x_1692_,
                                                                            v___f_1691_,
                                                                        );
                                                                    return v___x_1693_;
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v___x_1688_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_1648_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_1642_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_toBind_1617_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_asVar_1616_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_inst_1615_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_inst_1614_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_inst_1613_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_inst_1612_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_inst_1611_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_toPure_1610_,
                                                                    );
                                                                    v___x_1694_ =
                                                                        leanh::lean_apply_1(
                                                                            v_toVar_1608_,
                                                                            v_e_1609_,
                                                                        );
                                                                    return v___x_1694_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_1649_);
                                                leanh::lean_dec_ref(v_arg_1648_);
                                                leanh::lean_dec(v_toPure_1610_);
                                                leanh::lean_inc(v_toBind_1617_);
                                                leanh::lean_inc_ref(v_inst_1615_);
                                                leanh::lean_inc_ref(v_inst_1614_);
                                                leanh::lean_inc_ref(v_inst_1613_);
                                                leanh::lean_inc_ref(v_inst_1612_);
                                                leanh::lean_inc(v_inst_1611_);
                                                v___f_1695_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    0,
                                                    v_asVar_1616_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    1,
                                                    v_e_1609_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    2,
                                                    v_inst_1611_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    3,
                                                    v_inst_1612_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    4,
                                                    v_inst_1613_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    5,
                                                    v_inst_1614_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    6,
                                                    v_inst_1615_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    7,
                                                    v_toVar_1608_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    8,
                                                    v_arg_1638_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    9,
                                                    v_toBind_1617_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    10,
                                                    v___f_1618_,
                                                );
                                                v___x_1696_ =
                                                    l_Lean_Meta_Sym_Arith_isNegInst___redArg(
                                                        v_inst_1611_,
                                                        v_inst_1612_,
                                                        v_inst_1613_,
                                                        v_inst_1614_,
                                                        v_inst_1615_,
                                                        v_arg_1642_,
                                                    );
                                                v___x_1697_ = leanh::lean_apply_4(
                                                    v_toBind_1617_,
                                                    leanh::lean_box(0),
                                                    leanh::lean_box(0),
                                                    v___x_1696_,
                                                    v___f_1695_,
                                                );
                                                return v___x_1697_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_1649_);
                                            leanh::lean_dec_ref(v_arg_1648_);
                                            leanh::lean_dec(v___f_1618_);
                                            leanh::lean_dec_ref(v_inst_1612_);
                                            v___f_1698_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed as *mut core::ffi::c_void, 6, 5);
                                            leanh::lean_closure_set(
                                                v___f_1698_,
                                                0,
                                                v_asVar_1616_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_1698_,
                                                1,
                                                v_e_1609_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_1698_,
                                                2,
                                                v_arg_1638_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_1698_,
                                                3,
                                                v_toPure_1610_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_1698_,
                                                4,
                                                v_toVar_1608_,
                                            );
                                            v___x_1699_ =
                                                l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(
                                                    v_inst_1611_,
                                                    v_inst_1613_,
                                                    v_inst_1614_,
                                                    v_inst_1615_,
                                                    v_arg_1642_,
                                                );
                                            v___x_1700_ = leanh::lean_apply_4(
                                                v_toBind_1617_,
                                                leanh::lean_box(0),
                                                leanh::lean_box(0),
                                                v___x_1699_,
                                                v___f_1698_,
                                            );
                                            return v___x_1700_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_1649_);
                                        leanh::lean_dec_ref(v_arg_1648_);
                                        leanh::lean_dec(v___f_1618_);
                                        leanh::lean_dec_ref(v_inst_1612_);
                                        v___f_1701_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed as *mut core::ffi::c_void, 6, 5);
                                        leanh::lean_closure_set(
                                            v___f_1701_,
                                            0,
                                            v_asVar_1616_,
                                        );
                                        leanh::lean_closure_set(v___f_1701_, 1, v_e_1609_);
                                        leanh::lean_closure_set(v___f_1701_, 2, v_arg_1638_);
                                        leanh::lean_closure_set(
                                            v___f_1701_,
                                            3,
                                            v_toPure_1610_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1701_,
                                            4,
                                            v_toVar_1608_,
                                        );
                                        v___x_1702_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(
                                            v_inst_1611_,
                                            v_inst_1613_,
                                            v_inst_1614_,
                                            v_inst_1615_,
                                            v_arg_1642_,
                                        );
                                        v___x_1703_ = leanh::lean_apply_4(
                                            v_toBind_1617_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v___x_1702_,
                                            v___f_1701_,
                                        );
                                        return v___x_1703_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_1649_);
                                    leanh::lean_dec_ref(v_arg_1648_);
                                    leanh::lean_dec_ref(v_arg_1638_);
                                    leanh::lean_dec(v___f_1618_);
                                    leanh::lean_dec(v_toBind_1617_);
                                    leanh::lean_dec(v_asVar_1616_);
                                    leanh::lean_dec_ref(v_inst_1615_);
                                    leanh::lean_dec_ref(v_inst_1614_);
                                    leanh::lean_dec_ref(v_inst_1613_);
                                    leanh::lean_dec_ref(v_inst_1612_);
                                    leanh::lean_dec(v_inst_1611_);
                                    v_n_1621_ = v_arg_1642_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1643_);
                            leanh::lean_dec_ref(v_arg_1642_);
                            leanh::lean_dec(v___f_1618_);
                            leanh::lean_dec(v_toBind_1617_);
                            leanh::lean_dec(v_asVar_1616_);
                            leanh::lean_dec_ref(v_inst_1615_);
                            leanh::lean_dec_ref(v_inst_1614_);
                            leanh::lean_dec_ref(v_inst_1613_);
                            leanh::lean_dec_ref(v_inst_1612_);
                            leanh::lean_dec(v_inst_1611_);
                            v_n_1621_ = v_arg_1638_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_n_1621_) == 9 {
                    v_a_1622_ = leanh::lean_ctor_get(v_n_1621_, 0);
                    leanh::lean_inc_ref(v_a_1622_);
                    leanh::lean_dec_ref_known(v_n_1621_, 1);
                    if leanh::lean_obj_tag(v_a_1622_) == 0 {
                        leanh::lean_dec_ref(v_e_1609_);
                        leanh::lean_dec(v_toVar_1608_);
                        v_val_1623_ = leanh::lean_ctor_get(v_a_1622_, 0);
                        v_isSharedCheck_1632_ = (!leanh::lean_is_exclusive(v_a_1622_)) as u8;
                        if v_isSharedCheck_1632_ == 0 {
                            v___x_1625_ = v_a_1622_;
                            v_isShared_1626_ = v_isSharedCheck_1632_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1623_);
                            leanh::lean_dec(v_a_1622_);
                            v___x_1625_ = leanh::lean_box(0);
                            v_isShared_1626_ = v_isSharedCheck_1632_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_1622_);
                        leanh::lean_dec(v_toPure_1610_);
                        v___x_1633_ = leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                        return v___x_1633_;
                    }
                } else {
                    leanh::lean_dec_ref(v_n_1621_);
                    leanh::lean_dec(v_toPure_1610_);
                    v___x_1634_ = leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                    return v___x_1634_;
                }
            }
            2 => {
                v___x_1627_ = lean_nat_to_int(v_val_1623_);
                if v_isShared_1626_ == 0 {
                    leanh::lean_ctor_set(v___x_1625_, 0, v___x_1627_);
                    v___x_1629_ = v___x_1625_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1627_);
                    v___x_1629_ = v_reuseFailAlloc_1631_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1630_ = leanh::lean_apply_2(
                    v_toPure_1610_,
                    leanh::lean_box(0),
                    v___x_1629_,
                );
                return v___x_1630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
    mut v_inst_1704_: *mut leanh::LeanObject,
    mut v_inst_1705_: *mut leanh::LeanObject,
    mut v_inst_1706_: *mut leanh::LeanObject,
    mut v_inst_1707_: *mut leanh::LeanObject,
    mut v_inst_1708_: *mut leanh::LeanObject,
    mut v_toVar_1709_: *mut leanh::LeanObject,
    mut v_asVar_1710_: *mut leanh::LeanObject,
    mut v_e_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1712_ = leanh::lean_ctor_get(v_inst_1706_, 0);
    v_toBind_1713_ = leanh::lean_ctor_get(v_inst_1706_, 1);
    leanh::lean_inc_n(v_toBind_1713_, 2);
    v_toPure_1714_ = leanh::lean_ctor_get(v_toApplicative_1712_, 1);
    leanh::lean_inc_n(v_toPure_1714_, 2);
    leanh::lean_inc_ref(v_e_1711_);
    v___x_1715_ = leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1715_, 0, v_e_1711_);
    leanh::lean_inc(v_inst_1704_);
    v___x_1716_ = leanh::lean_apply_2(v_inst_1704_, leanh::lean_box(0), v___x_1715_);
    v___f_1717_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_1717_, 0, v_toPure_1714_);
    v___f_1718_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10 as *mut core::ffi::c_void, 12, 11);
    leanh::lean_closure_set(v___f_1718_, 0, v_toVar_1709_);
    leanh::lean_closure_set(v___f_1718_, 1, v_e_1711_);
    leanh::lean_closure_set(v___f_1718_, 2, v_toPure_1714_);
    leanh::lean_closure_set(v___f_1718_, 3, v_inst_1704_);
    leanh::lean_closure_set(v___f_1718_, 4, v_inst_1705_);
    leanh::lean_closure_set(v___f_1718_, 5, v_inst_1706_);
    leanh::lean_closure_set(v___f_1718_, 6, v_inst_1707_);
    leanh::lean_closure_set(v___f_1718_, 7, v_inst_1708_);
    leanh::lean_closure_set(v___f_1718_, 8, v_asVar_1710_);
    leanh::lean_closure_set(v___f_1718_, 9, v_toBind_1713_);
    leanh::lean_closure_set(v___f_1718_, 10, v___f_1717_);
    v___x_1719_ = leanh::lean_apply_4(
        v_toBind_1713_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1716_,
        v___f_1718_,
    );
    return v___x_1719_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(
    mut v_toPure_1720_: *mut leanh::LeanObject,
    mut v_inst_1721_: *mut leanh::LeanObject,
    mut v_inst_1722_: *mut leanh::LeanObject,
    mut v_inst_1723_: *mut leanh::LeanObject,
    mut v_inst_1724_: *mut leanh::LeanObject,
    mut v_inst_1725_: *mut leanh::LeanObject,
    mut v_toVar_1726_: *mut leanh::LeanObject,
    mut v_asVar_1727_: *mut leanh::LeanObject,
    mut v_arg_1728_: *mut leanh::LeanObject,
    mut v_toBind_1729_: *mut leanh::LeanObject,
    mut v_____do__lift_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1731_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_1731_, 0, v_____do__lift_1730_);
    leanh::lean_closure_set(v___f_1731_, 1, v_toPure_1720_);
    v___x_1732_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1721_,
            v_inst_1722_,
            v_inst_1723_,
            v_inst_1724_,
            v_inst_1725_,
            v_toVar_1726_,
            v_asVar_1727_,
            v_arg_1728_,
        );
    v___x_1733_ = leanh::lean_apply_4(
        v_toBind_1729_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1732_,
        v___f_1731_,
    );
    return v___x_1733_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(
    mut v_m_1734_: *mut leanh::LeanObject,
    mut v_inst_1735_: *mut leanh::LeanObject,
    mut v_inst_1736_: *mut leanh::LeanObject,
    mut v_inst_1737_: *mut leanh::LeanObject,
    mut v_inst_1738_: *mut leanh::LeanObject,
    mut v_inst_1739_: *mut leanh::LeanObject,
    mut v_toVar_1740_: *mut leanh::LeanObject,
    mut v_asVar_1741_: *mut leanh::LeanObject,
    mut v_e_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1735_,
            v_inst_1736_,
            v_inst_1737_,
            v_inst_1738_,
            v_inst_1739_,
            v_toVar_1740_,
            v_asVar_1741_,
            v_e_1742_,
        );
    return v___x_1743_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0(
    mut v_toPure_1744_: *mut leanh::LeanObject,
    mut v_____do__lift_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1746_, 0, v_____do__lift_1745_);
    v___x_1747_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1747_, 0, v___x_1746_);
    v___x_1748_ =
        leanh::lean_apply_2(v_toPure_1744_, leanh::lean_box(0), v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(
    mut v_toPure_1749_: *mut leanh::LeanObject,
    mut v_____do__lift_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1751_, 0, v_____do__lift_1750_);
    v___x_1752_ =
        leanh::lean_apply_2(v_toPure_1749_, leanh::lean_box(0), v___x_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(
    mut v_toPure_1753_: *mut leanh::LeanObject,
    mut v_____do__lift_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1755_, 0, v_____do__lift_1754_);
    v___x_1756_ =
        leanh::lean_apply_2(v_toPure_1753_, leanh::lean_box(0), v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(
    mut v_inst_1757_: *mut leanh::LeanObject,
    mut v_e_1758_: *mut leanh::LeanObject,
    mut v_toBind_1759_: *mut leanh::LeanObject,
    mut v___f_1760_: *mut leanh::LeanObject,
    mut v_____r_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = leanh::lean_apply_1(v_inst_1757_, v_e_1758_);
    v___x_1763_ = leanh::lean_apply_4(
        v_toBind_1759_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1762_,
        v___f_1760_,
    );
    return v___x_1763_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(
    mut v_inst_1764_: *mut leanh::LeanObject,
    mut v_toBind_1765_: *mut leanh::LeanObject,
    mut v___f_1766_: *mut leanh::LeanObject,
    mut v_inst_1767_: *mut leanh::LeanObject,
    mut v_e_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_1765_);
    leanh::lean_inc_ref(v_e_1768_);
    v___f_1769_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1769_, 0, v_inst_1764_);
    leanh::lean_closure_set(v___f_1769_, 1, v_e_1768_);
    leanh::lean_closure_set(v___f_1769_, 2, v_toBind_1765_);
    leanh::lean_closure_set(v___f_1769_, 3, v___f_1766_);
    v___x_1770_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
            v_inst_1767_,
            v_e_1768_,
        );
    v___x_1771_ = leanh::lean_apply_4(
        v_toBind_1765_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1770_,
        v___f_1769_,
    );
    return v___x_1771_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(
    mut v_inst_1772_: *mut leanh::LeanObject,
    mut v_toBind_1773_: *mut leanh::LeanObject,
    mut v___f_1774_: *mut leanh::LeanObject,
    mut v_e_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = leanh::lean_apply_1(v_inst_1772_, v_e_1775_);
    v___x_1777_ = leanh::lean_apply_4(
        v_toBind_1773_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1776_,
        v___f_1774_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(
    mut v_skipVar_1778_: u8,
    mut v_toVar_1779_: *mut leanh::LeanObject,
    mut v_toBind_1780_: *mut leanh::LeanObject,
    mut v___f_1781_: *mut leanh::LeanObject,
    mut v_toPure_1782_: *mut leanh::LeanObject,
    mut v_e_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_skipVar_1778_ == 0 {
        let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1782_);
        v___x_1784_ = leanh::lean_apply_1(v_toVar_1779_, v_e_1783_);
        v___x_1785_ = leanh::lean_apply_4(
            v_toBind_1780_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1784_,
            v___f_1781_,
        );
        return v___x_1785_;
    } else {
        let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_1783_);
        leanh::lean_dec(v___f_1781_);
        leanh::lean_dec(v_toBind_1780_);
        leanh::lean_dec(v_toVar_1779_);
        v___x_1786_ = leanh::lean_box(0);
        v___x_1787_ =
            leanh::lean_apply_2(v_toPure_1782_, leanh::lean_box(0), v___x_1786_);
        return v___x_1787_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(
    mut v_skipVar_1788_: *mut leanh::LeanObject,
    mut v_toVar_1789_: *mut leanh::LeanObject,
    mut v_toBind_1790_: *mut leanh::LeanObject,
    mut v___f_1791_: *mut leanh::LeanObject,
    mut v_toPure_1792_: *mut leanh::LeanObject,
    mut v_e_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipVar_boxed_1794_: u8 = 0;
    let mut v_res_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_1794_ = (leanh::lean_unbox(v_skipVar_1788_) as u8);
    v_res_1795_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(
        v_skipVar_boxed_1794_,
        v_toVar_1789_,
        v_toBind_1790_,
        v___f_1791_,
        v_toPure_1792_,
        v_e_1793_,
    );
    return v_res_1795_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7(
    mut v_toTopVar_1796_: *mut leanh::LeanObject,
    mut v_e_1797_: *mut leanh::LeanObject,
    mut v_____r_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = leanh::lean_apply_1(v_toTopVar_1796_, v_e_1797_);
    return v___x_1799_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(
    mut v_toTopVar_1800_: *mut leanh::LeanObject,
    mut v_inst_1801_: *mut leanh::LeanObject,
    mut v_toBind_1802_: *mut leanh::LeanObject,
    mut v_e_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_e_1803_);
    v___f_1804_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1804_, 0, v_toTopVar_1800_);
    leanh::lean_closure_set(v___f_1804_, 1, v_e_1803_);
    v___x_1805_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
            v_inst_1801_,
            v_e_1803_,
        );
    v___x_1806_ = leanh::lean_apply_4(
        v_toBind_1802_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1805_,
        v___f_1804_,
    );
    return v___x_1806_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(
    mut v_____do__lift_1807_: *mut leanh::LeanObject,
    mut v_toPure_1808_: *mut leanh::LeanObject,
    mut v_____do__lift_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1810_, 0, v_____do__lift_1807_);
    leanh::lean_ctor_set(v___x_1810_, 1, v_____do__lift_1809_);
    v___x_1811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    v___x_1812_ =
        leanh::lean_apply_2(v_toPure_1808_, leanh::lean_box(0), v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(
    mut v_toPure_1813_: *mut leanh::LeanObject,
    mut v_inst_1814_: *mut leanh::LeanObject,
    mut v_inst_1815_: *mut leanh::LeanObject,
    mut v_inst_1816_: *mut leanh::LeanObject,
    mut v_inst_1817_: *mut leanh::LeanObject,
    mut v_inst_1818_: *mut leanh::LeanObject,
    mut v_toVar_1819_: *mut leanh::LeanObject,
    mut v_asVar_1820_: *mut leanh::LeanObject,
    mut v_arg_1821_: *mut leanh::LeanObject,
    mut v_toBind_1822_: *mut leanh::LeanObject,
    mut v_____do__lift_1823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1824_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1824_, 0, v_____do__lift_1823_);
    leanh::lean_closure_set(v___f_1824_, 1, v_toPure_1813_);
    v___x_1825_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1814_,
            v_inst_1815_,
            v_inst_1816_,
            v_inst_1817_,
            v_inst_1818_,
            v_toVar_1819_,
            v_asVar_1820_,
            v_arg_1821_,
        );
    v___x_1826_ = leanh::lean_apply_4(
        v_toBind_1822_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1825_,
        v___f_1824_,
    );
    return v___x_1826_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(
    mut v_asTopVar_1827_: *mut leanh::LeanObject,
    mut v_e_1828_: *mut leanh::LeanObject,
    mut v_inst_1829_: *mut leanh::LeanObject,
    mut v_inst_1830_: *mut leanh::LeanObject,
    mut v_inst_1831_: *mut leanh::LeanObject,
    mut v_inst_1832_: *mut leanh::LeanObject,
    mut v_inst_1833_: *mut leanh::LeanObject,
    mut v_toVar_1834_: *mut leanh::LeanObject,
    mut v_asVar_1835_: *mut leanh::LeanObject,
    mut v_arg_1836_: *mut leanh::LeanObject,
    mut v_toBind_1837_: *mut leanh::LeanObject,
    mut v___f_1838_: *mut leanh::LeanObject,
    mut v_____do__lift_1839_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1839_ == 0 {
        let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_1838_);
        leanh::lean_dec(v_toBind_1837_);
        leanh::lean_dec_ref(v_arg_1836_);
        leanh::lean_dec(v_asVar_1835_);
        leanh::lean_dec(v_toVar_1834_);
        leanh::lean_dec_ref(v_inst_1833_);
        leanh::lean_dec_ref(v_inst_1832_);
        leanh::lean_dec_ref(v_inst_1831_);
        leanh::lean_dec_ref(v_inst_1830_);
        leanh::lean_dec(v_inst_1829_);
        v___x_1840_ = leanh::lean_apply_1(v_asTopVar_1827_, v_e_1828_);
        return v___x_1840_;
    } else {
        let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_1828_);
        leanh::lean_dec(v_asTopVar_1827_);
        v___x_1841_ =
            l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
                v_inst_1829_,
                v_inst_1830_,
                v_inst_1831_,
                v_inst_1832_,
                v_inst_1833_,
                v_toVar_1834_,
                v_asVar_1835_,
                v_arg_1836_,
            );
        v___x_1842_ = leanh::lean_apply_4(
            v_toBind_1837_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1841_,
            v___f_1838_,
        );
        return v___x_1842_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(
    mut v_asTopVar_1843_: *mut leanh::LeanObject,
    mut v_e_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_inst_1846_: *mut leanh::LeanObject,
    mut v_inst_1847_: *mut leanh::LeanObject,
    mut v_inst_1848_: *mut leanh::LeanObject,
    mut v_inst_1849_: *mut leanh::LeanObject,
    mut v_toVar_1850_: *mut leanh::LeanObject,
    mut v_asVar_1851_: *mut leanh::LeanObject,
    mut v_arg_1852_: *mut leanh::LeanObject,
    mut v_toBind_1853_: *mut leanh::LeanObject,
    mut v___f_1854_: *mut leanh::LeanObject,
    mut v_____do__lift_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_4902__boxed_1856_: u8 = 0;
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4902__boxed_1856_ = (leanh::lean_unbox(v_____do__lift_1855_) as u8);
    v_res_1857_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(
        v_asTopVar_1843_,
        v_e_1844_,
        v_inst_1845_,
        v_inst_1846_,
        v_inst_1847_,
        v_inst_1848_,
        v_inst_1849_,
        v_toVar_1850_,
        v_asVar_1851_,
        v_arg_1852_,
        v_toBind_1853_,
        v___f_1854_,
        v_____do__lift_4902__boxed_1856_,
    );
    return v_res_1857_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12(
    mut v_____do__lift_1858_: *mut leanh::LeanObject,
    mut v_toPure_1859_: *mut leanh::LeanObject,
    mut v_____do__lift_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1861_, 0, v_____do__lift_1858_);
    leanh::lean_ctor_set(v___x_1861_, 1, v_____do__lift_1860_);
    v___x_1862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    v___x_1863_ =
        leanh::lean_apply_2(v_toPure_1859_, leanh::lean_box(0), v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(
    mut v_toPure_1864_: *mut leanh::LeanObject,
    mut v_inst_1865_: *mut leanh::LeanObject,
    mut v_inst_1866_: *mut leanh::LeanObject,
    mut v_inst_1867_: *mut leanh::LeanObject,
    mut v_inst_1868_: *mut leanh::LeanObject,
    mut v_inst_1869_: *mut leanh::LeanObject,
    mut v_toVar_1870_: *mut leanh::LeanObject,
    mut v_asVar_1871_: *mut leanh::LeanObject,
    mut v_arg_1872_: *mut leanh::LeanObject,
    mut v_toBind_1873_: *mut leanh::LeanObject,
    mut v_____do__lift_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1875_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1875_, 0, v_____do__lift_1874_);
    leanh::lean_closure_set(v___f_1875_, 1, v_toPure_1864_);
    v___x_1876_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1865_,
            v_inst_1866_,
            v_inst_1867_,
            v_inst_1868_,
            v_inst_1869_,
            v_toVar_1870_,
            v_asVar_1871_,
            v_arg_1872_,
        );
    v___x_1877_ = leanh::lean_apply_4(
        v_toBind_1873_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1876_,
        v___f_1875_,
    );
    return v___x_1877_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(
    mut v_____do__lift_1878_: *mut leanh::LeanObject,
    mut v_toPure_1879_: *mut leanh::LeanObject,
    mut v_____do__lift_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1881_, 0, v_____do__lift_1878_);
    leanh::lean_ctor_set(v___x_1881_, 1, v_____do__lift_1880_);
    v___x_1882_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
    v___x_1883_ =
        leanh::lean_apply_2(v_toPure_1879_, leanh::lean_box(0), v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(
    mut v_toPure_1884_: *mut leanh::LeanObject,
    mut v_inst_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_inst_1887_: *mut leanh::LeanObject,
    mut v_inst_1888_: *mut leanh::LeanObject,
    mut v_inst_1889_: *mut leanh::LeanObject,
    mut v_toVar_1890_: *mut leanh::LeanObject,
    mut v_asVar_1891_: *mut leanh::LeanObject,
    mut v_arg_1892_: *mut leanh::LeanObject,
    mut v_toBind_1893_: *mut leanh::LeanObject,
    mut v_____do__lift_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1895_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1895_, 0, v_____do__lift_1894_);
    leanh::lean_closure_set(v___f_1895_, 1, v_toPure_1884_);
    v___x_1896_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
            v_inst_1885_,
            v_inst_1886_,
            v_inst_1887_,
            v_inst_1888_,
            v_inst_1889_,
            v_toVar_1890_,
            v_asVar_1891_,
            v_arg_1892_,
        );
    v___x_1897_ = leanh::lean_apply_4(
        v_toBind_1893_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1896_,
        v___f_1895_,
    );
    return v___x_1897_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(
    mut v_val_1898_: *mut leanh::LeanObject,
    mut v_toPure_1899_: *mut leanh::LeanObject,
    mut v_____do__lift_1900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1901_, 0, v_____do__lift_1900_);
    leanh::lean_ctor_set(v___x_1901_, 1, v_val_1898_);
    v___x_1902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1902_, 0, v___x_1901_);
    v___x_1903_ =
        leanh::lean_apply_2(v_toPure_1899_, leanh::lean_box(0), v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(
    mut v_asTopVar_1904_: *mut leanh::LeanObject,
    mut v_e_1905_: *mut leanh::LeanObject,
    mut v_arg_1906_: *mut leanh::LeanObject,
    mut v_toPure_1907_: *mut leanh::LeanObject,
    mut v_toTopVar_1908_: *mut leanh::LeanObject,
    mut v_____do__lift_1909_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1909_ == 0 {
                    leanh::lean_dec(v_toTopVar_1908_);
                    leanh::lean_dec(v_toPure_1907_);
                    leanh::lean_dec_ref(v_arg_1906_);
                    v___x_1910_ = leanh::lean_apply_1(v_asTopVar_1904_, v_e_1905_);
                    return v___x_1910_;
                } else {
                    leanh::lean_dec(v_asTopVar_1904_);
                    v___x_1911_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_1906_);
                    if leanh::lean_obj_tag(v___x_1911_) == 1 {
                        leanh::lean_dec(v_toTopVar_1908_);
                        leanh::lean_dec_ref(v_e_1905_);
                        v_val_1912_ = leanh::lean_ctor_get(v___x_1911_, 0);
                        v_isSharedCheck_1921_ =
                            (!leanh::lean_is_exclusive(v___x_1911_)) as u8;
                        if v_isSharedCheck_1921_ == 0 {
                            v___x_1914_ = v___x_1911_;
                            v_isShared_1915_ = v_isSharedCheck_1921_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1912_);
                            leanh::lean_dec(v___x_1911_);
                            v___x_1914_ = leanh::lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1921_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1911_);
                        leanh::lean_dec(v_toPure_1907_);
                        v___x_1922_ = leanh::lean_apply_1(v_toTopVar_1908_, v_e_1905_);
                        return v___x_1922_;
                    }
                }
            }
            1 => {
                v___x_1916_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1916_, 0, v_val_1912_);
                if v_isShared_1915_ == 0 {
                    leanh::lean_ctor_set(v___x_1914_, 0, v___x_1916_);
                    v___x_1918_ = v___x_1914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1916_);
                    v___x_1918_ = v_reuseFailAlloc_1920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1919_ = leanh::lean_apply_2(
                    v_toPure_1907_,
                    leanh::lean_box(0),
                    v___x_1918_,
                );
                return v___x_1919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(
    mut v_asTopVar_1923_: *mut leanh::LeanObject,
    mut v_e_1924_: *mut leanh::LeanObject,
    mut v_arg_1925_: *mut leanh::LeanObject,
    mut v_toPure_1926_: *mut leanh::LeanObject,
    mut v_toTopVar_1927_: *mut leanh::LeanObject,
    mut v_____do__lift_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_4996__boxed_1929_: u8 = 0;
    let mut v_res_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4996__boxed_1929_ = (leanh::lean_unbox(v_____do__lift_1928_) as u8);
    v_res_1930_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(
        v_asTopVar_1923_,
        v_e_1924_,
        v_arg_1925_,
        v_toPure_1926_,
        v_toTopVar_1927_,
        v_____do__lift_4996__boxed_1929_,
    );
    return v_res_1930_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(
    mut v_asTopVar_1931_: *mut leanh::LeanObject,
    mut v_e_1932_: *mut leanh::LeanObject,
    mut v_arg_1933_: *mut leanh::LeanObject,
    mut v_toPure_1934_: *mut leanh::LeanObject,
    mut v_toTopVar_1935_: *mut leanh::LeanObject,
    mut v_____do__lift_1936_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1936_ == 0 {
                    leanh::lean_dec(v_toTopVar_1935_);
                    leanh::lean_dec(v_toPure_1934_);
                    leanh::lean_dec_ref(v_arg_1933_);
                    v___x_1937_ = leanh::lean_apply_1(v_asTopVar_1931_, v_e_1932_);
                    return v___x_1937_;
                } else {
                    leanh::lean_dec(v_asTopVar_1931_);
                    v___x_1938_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1933_);
                    if leanh::lean_obj_tag(v___x_1938_) == 1 {
                        leanh::lean_dec(v_toTopVar_1935_);
                        leanh::lean_dec_ref(v_e_1932_);
                        v_val_1939_ = leanh::lean_ctor_get(v___x_1938_, 0);
                        v_isSharedCheck_1948_ =
                            (!leanh::lean_is_exclusive(v___x_1938_)) as u8;
                        if v_isSharedCheck_1948_ == 0 {
                            v___x_1941_ = v___x_1938_;
                            v_isShared_1942_ = v_isSharedCheck_1948_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1939_);
                            leanh::lean_dec(v___x_1938_);
                            v___x_1941_ = leanh::lean_box(0);
                            v_isShared_1942_ = v_isSharedCheck_1948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1938_);
                        leanh::lean_dec(v_toPure_1934_);
                        v___x_1949_ = leanh::lean_apply_1(v_toTopVar_1935_, v_e_1932_);
                        return v___x_1949_;
                    }
                }
            }
            1 => {
                v___x_1943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1943_, 0, v_val_1939_);
                if v_isShared_1942_ == 0 {
                    leanh::lean_ctor_set(v___x_1941_, 0, v___x_1943_);
                    v___x_1945_ = v___x_1941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1943_);
                    v___x_1945_ = v_reuseFailAlloc_1947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1946_ = leanh::lean_apply_2(
                    v_toPure_1934_,
                    leanh::lean_box(0),
                    v___x_1945_,
                );
                return v___x_1946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(
    mut v_asTopVar_1950_: *mut leanh::LeanObject,
    mut v_e_1951_: *mut leanh::LeanObject,
    mut v_arg_1952_: *mut leanh::LeanObject,
    mut v_toPure_1953_: *mut leanh::LeanObject,
    mut v_toTopVar_1954_: *mut leanh::LeanObject,
    mut v_____do__lift_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_5028__boxed_1956_: u8 = 0;
    let mut v_res_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_5028__boxed_1956_ = (leanh::lean_unbox(v_____do__lift_1955_) as u8);
    v_res_1957_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(
        v_asTopVar_1950_,
        v_e_1951_,
        v_arg_1952_,
        v_toPure_1953_,
        v_toTopVar_1954_,
        v_____do__lift_5028__boxed_1956_,
    );
    return v_res_1957_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(
    mut v_toTopVar_1958_: *mut leanh::LeanObject,
    mut v_e_1959_: *mut leanh::LeanObject,
    mut v_toPure_1960_: *mut leanh::LeanObject,
    mut v_inst_1961_: *mut leanh::LeanObject,
    mut v_inst_1962_: *mut leanh::LeanObject,
    mut v_inst_1963_: *mut leanh::LeanObject,
    mut v_inst_1964_: *mut leanh::LeanObject,
    mut v_inst_1965_: *mut leanh::LeanObject,
    mut v_toVar_1966_: *mut leanh::LeanObject,
    mut v_asVar_1967_: *mut leanh::LeanObject,
    mut v_toBind_1968_: *mut leanh::LeanObject,
    mut v_asTopVar_1969_: *mut leanh::LeanObject,
    mut v___f_1970_: *mut leanh::LeanObject,
    mut v_____x_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: u8 = 0;
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1972_ = l_Lean_Expr_cleanupAnnotations(v_____x_1971_);
                v___x_1973_ = l_Lean_Expr_isApp(v___x_1972_);
                if v___x_1973_ == 0 {
                    leanh::lean_dec_ref(v___x_1972_);
                    leanh::lean_dec(v___f_1970_);
                    leanh::lean_dec(v_asTopVar_1969_);
                    leanh::lean_dec(v_toBind_1968_);
                    leanh::lean_dec(v_asVar_1967_);
                    leanh::lean_dec(v_toVar_1966_);
                    leanh::lean_dec_ref(v_inst_1965_);
                    leanh::lean_dec_ref(v_inst_1964_);
                    leanh::lean_dec_ref(v_inst_1963_);
                    leanh::lean_dec_ref(v_inst_1962_);
                    leanh::lean_dec(v_inst_1961_);
                    leanh::lean_dec(v_toPure_1960_);
                    v___x_1974_ = leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                    return v___x_1974_;
                } else {
                    v_arg_1975_ = leanh::lean_ctor_get(v___x_1972_, 1);
                    leanh::lean_inc_ref(v_arg_1975_);
                    v___x_1976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1972_);
                    v___x_1977_ = l_Lean_Expr_isApp(v___x_1976_);
                    if v___x_1977_ == 0 {
                        leanh::lean_dec_ref(v___x_1976_);
                        leanh::lean_dec_ref(v_arg_1975_);
                        leanh::lean_dec(v___f_1970_);
                        leanh::lean_dec(v_asTopVar_1969_);
                        leanh::lean_dec(v_toBind_1968_);
                        leanh::lean_dec(v_asVar_1967_);
                        leanh::lean_dec(v_toVar_1966_);
                        leanh::lean_dec_ref(v_inst_1965_);
                        leanh::lean_dec_ref(v_inst_1964_);
                        leanh::lean_dec_ref(v_inst_1963_);
                        leanh::lean_dec_ref(v_inst_1962_);
                        leanh::lean_dec(v_inst_1961_);
                        leanh::lean_dec(v_toPure_1960_);
                        v___x_1978_ = leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                        return v___x_1978_;
                    } else {
                        v_arg_1979_ = leanh::lean_ctor_get(v___x_1976_, 1);
                        leanh::lean_inc_ref(v_arg_1979_);
                        v___x_1980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1976_);
                        v___x_1981_ = l_Lean_Expr_isApp(v___x_1980_);
                        if v___x_1981_ == 0 {
                            leanh::lean_dec_ref(v___x_1980_);
                            leanh::lean_dec_ref(v_arg_1979_);
                            leanh::lean_dec_ref(v_arg_1975_);
                            leanh::lean_dec(v___f_1970_);
                            leanh::lean_dec(v_asTopVar_1969_);
                            leanh::lean_dec(v_toBind_1968_);
                            leanh::lean_dec(v_asVar_1967_);
                            leanh::lean_dec(v_toVar_1966_);
                            leanh::lean_dec_ref(v_inst_1965_);
                            leanh::lean_dec_ref(v_inst_1964_);
                            leanh::lean_dec_ref(v_inst_1963_);
                            leanh::lean_dec_ref(v_inst_1962_);
                            leanh::lean_dec(v_inst_1961_);
                            leanh::lean_dec(v_toPure_1960_);
                            v___x_1982_ = leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                            return v___x_1982_;
                        } else {
                            v_arg_1983_ = leanh::lean_ctor_get(v___x_1980_, 1);
                            leanh::lean_inc_ref(v_arg_1983_);
                            v___x_1984_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1980_);
                            v___x_1985_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4;
                            v___x_1986_ = l_Lean_Expr_isConstOf(v___x_1984_, v___x_1985_);
                            if v___x_1986_ == 0 {
                                v___x_1987_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7;
                                v___x_1988_ = l_Lean_Expr_isConstOf(v___x_1984_, v___x_1987_);
                                if v___x_1988_ == 0 {
                                    v___x_1989_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10;
                                    v___x_1990_ = l_Lean_Expr_isConstOf(v___x_1984_, v___x_1989_);
                                    if v___x_1990_ == 0 {
                                        v___x_1991_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13;
                                        v___x_1992_ =
                                            l_Lean_Expr_isConstOf(v___x_1984_, v___x_1991_);
                                        if v___x_1992_ == 0 {
                                            leanh::lean_dec(v___f_1970_);
                                            v___x_1993_ = l_Lean_Expr_isApp(v___x_1984_);
                                            if v___x_1993_ == 0 {
                                                leanh::lean_dec_ref(v___x_1984_);
                                                leanh::lean_dec_ref(v_arg_1983_);
                                                leanh::lean_dec_ref(v_arg_1979_);
                                                leanh::lean_dec_ref(v_arg_1975_);
                                                leanh::lean_dec(v_asTopVar_1969_);
                                                leanh::lean_dec(v_toBind_1968_);
                                                leanh::lean_dec(v_asVar_1967_);
                                                leanh::lean_dec(v_toVar_1966_);
                                                leanh::lean_dec_ref(v_inst_1965_);
                                                leanh::lean_dec_ref(v_inst_1964_);
                                                leanh::lean_dec_ref(v_inst_1963_);
                                                leanh::lean_dec_ref(v_inst_1962_);
                                                leanh::lean_dec(v_inst_1961_);
                                                leanh::lean_dec(v_toPure_1960_);
                                                v___x_1994_ = leanh::lean_apply_1(
                                                    v_toTopVar_1958_,
                                                    v_e_1959_,
                                                );
                                                return v___x_1994_;
                                            } else {
                                                v___x_1995_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_1984_);
                                                v___x_1996_ = l_Lean_Expr_isApp(v___x_1995_);
                                                if v___x_1996_ == 0 {
                                                    leanh::lean_dec_ref(v___x_1995_);
                                                    leanh::lean_dec_ref(v_arg_1983_);
                                                    leanh::lean_dec_ref(v_arg_1979_);
                                                    leanh::lean_dec_ref(v_arg_1975_);
                                                    leanh::lean_dec(v_asTopVar_1969_);
                                                    leanh::lean_dec(v_toBind_1968_);
                                                    leanh::lean_dec(v_asVar_1967_);
                                                    leanh::lean_dec(v_toVar_1966_);
                                                    leanh::lean_dec_ref(v_inst_1965_);
                                                    leanh::lean_dec_ref(v_inst_1964_);
                                                    leanh::lean_dec_ref(v_inst_1963_);
                                                    leanh::lean_dec_ref(v_inst_1962_);
                                                    leanh::lean_dec(v_inst_1961_);
                                                    leanh::lean_dec(v_toPure_1960_);
                                                    v___x_1997_ = leanh::lean_apply_1(
                                                        v_toTopVar_1958_,
                                                        v_e_1959_,
                                                    );
                                                    return v___x_1997_;
                                                } else {
                                                    v___x_1998_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1995_,
                                                    );
                                                    v___x_1999_ = l_Lean_Expr_isApp(v___x_1998_);
                                                    if v___x_1999_ == 0 {
                                                        leanh::lean_dec_ref(v___x_1998_);
                                                        leanh::lean_dec_ref(v_arg_1983_);
                                                        leanh::lean_dec_ref(v_arg_1979_);
                                                        leanh::lean_dec_ref(v_arg_1975_);
                                                        leanh::lean_dec(v_asTopVar_1969_);
                                                        leanh::lean_dec(v_toBind_1968_);
                                                        leanh::lean_dec(v_asVar_1967_);
                                                        leanh::lean_dec(v_toVar_1966_);
                                                        leanh::lean_dec_ref(v_inst_1965_);
                                                        leanh::lean_dec_ref(v_inst_1964_);
                                                        leanh::lean_dec_ref(v_inst_1963_);
                                                        leanh::lean_dec_ref(v_inst_1962_);
                                                        leanh::lean_dec(v_inst_1961_);
                                                        leanh::lean_dec(v_toPure_1960_);
                                                        v___x_2000_ = leanh::lean_apply_1(
                                                            v_toTopVar_1958_,
                                                            v_e_1959_,
                                                        );
                                                        return v___x_2000_;
                                                    } else {
                                                        v___x_2001_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1998_,
                                                            );
                                                        v___x_2002_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16;
                                                        v___x_2003_ = l_Lean_Expr_isConstOf(
                                                            v___x_2001_,
                                                            v___x_2002_,
                                                        );
                                                        if v___x_2003_ == 0 {
                                                            v___x_2004_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19;
                                                            v___x_2005_ = l_Lean_Expr_isConstOf(
                                                                v___x_2001_,
                                                                v___x_2004_,
                                                            );
                                                            if v___x_2005_ == 0 {
                                                                v___x_2006_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22;
                                                                v___x_2007_ = l_Lean_Expr_isConstOf(
                                                                    v___x_2001_,
                                                                    v___x_2006_,
                                                                );
                                                                if v___x_2007_ == 0 {
                                                                    v___x_2008_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25;
                                                                    v___x_2009_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_2001_,
                                                                            v___x_2008_,
                                                                        );
                                                                    leanh::lean_dec_ref(
                                                                        v___x_2001_,
                                                                    );
                                                                    if v___x_2009_ == 0 {
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1983_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1979_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1975_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_asTopVar_1969_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_toBind_1968_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_asVar_1967_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_toVar_1966_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_inst_1965_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_inst_1964_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_inst_1963_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_inst_1962_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_inst_1961_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_toPure_1960_,
                                                                        );
                                                                        v___x_2010_ = leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                                                                        return v___x_2010_;
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_toTopVar_1958_,
                                                                        );
                                                                        leanh::lean_inc_n(
                                                                            v_toBind_1968_,
                                                                            2,
                                                                        );
                                                                        leanh::lean_inc(
                                                                            v_asVar_1967_,
                                                                        );
                                                                        leanh::lean_inc(
                                                                            v_toVar_1966_,
                                                                        );
                                                                        leanh::lean_inc_ref_n(v_inst_1965_, 2);
                                                                        leanh::lean_inc_ref_n(v_inst_1964_, 2);
                                                                        leanh::lean_inc_ref_n(v_inst_1963_, 2);
                                                                        leanh::lean_inc_ref_n(v_inst_1962_, 2);
                                                                        leanh::lean_inc_n(
                                                                            v_inst_1961_,
                                                                            2,
                                                                        );
                                                                        v___f_2011_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10 as *mut core::ffi::c_void, 11, 10);
                                                                        leanh::lean_closure_set(v___f_2011_, 0, v_toPure_1960_);
                                                                        leanh::lean_closure_set(v___f_2011_, 1, v_inst_1961_);
                                                                        leanh::lean_closure_set(v___f_2011_, 2, v_inst_1962_);
                                                                        leanh::lean_closure_set(v___f_2011_, 3, v_inst_1963_);
                                                                        leanh::lean_closure_set(v___f_2011_, 4, v_inst_1964_);
                                                                        leanh::lean_closure_set(v___f_2011_, 5, v_inst_1965_);
                                                                        leanh::lean_closure_set(v___f_2011_, 6, v_toVar_1966_);
                                                                        leanh::lean_closure_set(v___f_2011_, 7, v_asVar_1967_);
                                                                        leanh::lean_closure_set(v___f_2011_, 8, v_arg_1975_);
                                                                        leanh::lean_closure_set(v___f_2011_, 9, v_toBind_1968_);
                                                                        v___f_2012_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                        leanh::lean_closure_set(v___f_2012_, 0, v_asTopVar_1969_);
                                                                        leanh::lean_closure_set(v___f_2012_, 1, v_e_1959_);
                                                                        leanh::lean_closure_set(v___f_2012_, 2, v_inst_1961_);
                                                                        leanh::lean_closure_set(v___f_2012_, 3, v_inst_1962_);
                                                                        leanh::lean_closure_set(v___f_2012_, 4, v_inst_1963_);
                                                                        leanh::lean_closure_set(v___f_2012_, 5, v_inst_1964_);
                                                                        leanh::lean_closure_set(v___f_2012_, 6, v_inst_1965_);
                                                                        leanh::lean_closure_set(v___f_2012_, 7, v_toVar_1966_);
                                                                        leanh::lean_closure_set(v___f_2012_, 8, v_asVar_1967_);
                                                                        leanh::lean_closure_set(v___f_2012_, 9, v_arg_1979_);
                                                                        leanh::lean_closure_set(v___f_2012_, 10, v_toBind_1968_);
                                                                        leanh::lean_closure_set(v___f_2012_, 11, v___f_2011_);
                                                                        v___x_2013_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                        v___x_2014_ = leanh::lean_apply_4(v_toBind_1968_, leanh::lean_box(0), leanh::lean_box(0), v___x_2013_, v___f_2012_);
                                                                        return v___x_2014_;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_2001_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_toTopVar_1958_,
                                                                    );
                                                                    leanh::lean_inc_n(
                                                                        v_toBind_1968_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_asVar_1967_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_toVar_1966_,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1965_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1964_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1963_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_ref_n(
                                                                        v_inst_1962_,
                                                                        2,
                                                                    );
                                                                    leanh::lean_inc_n(
                                                                        v_inst_1961_,
                                                                        2,
                                                                    );
                                                                    v___f_2015_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13 as *mut core::ffi::c_void, 11, 10);
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        0,
                                                                        v_toPure_1960_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        1,
                                                                        v_inst_1961_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        2,
                                                                        v_inst_1962_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        3,
                                                                        v_inst_1963_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        4,
                                                                        v_inst_1964_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        5,
                                                                        v_inst_1965_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        6,
                                                                        v_toVar_1966_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        7,
                                                                        v_asVar_1967_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        8,
                                                                        v_arg_1975_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        9,
                                                                        v_toBind_1968_,
                                                                    );
                                                                    v___f_2016_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        0,
                                                                        v_asTopVar_1969_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        1,
                                                                        v_e_1959_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        2,
                                                                        v_inst_1961_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        3,
                                                                        v_inst_1962_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        4,
                                                                        v_inst_1963_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        5,
                                                                        v_inst_1964_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        6,
                                                                        v_inst_1965_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        7,
                                                                        v_toVar_1966_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        8,
                                                                        v_asVar_1967_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        9,
                                                                        v_arg_1979_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        10,
                                                                        v_toBind_1968_,
                                                                    );
                                                                    leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        11,
                                                                        v___f_2015_,
                                                                    );
                                                                    v___x_2017_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                    v___x_2018_ =
                                                                        leanh::lean_apply_4(
                                                                            v_toBind_1968_,
                                                                            leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            v___x_2017_,
                                                                            v___f_2016_,
                                                                        );
                                                                    return v___x_2018_;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_2001_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_toTopVar_1958_,
                                                                );
                                                                leanh::lean_inc_n(
                                                                    v_toBind_1968_,
                                                                    2,
                                                                );
                                                                leanh::lean_inc(
                                                                    v_asVar_1967_,
                                                                );
                                                                leanh::lean_inc(
                                                                    v_toVar_1966_,
                                                                );
                                                                leanh::lean_inc_ref_n(
                                                                    v_inst_1965_,
                                                                    2,
                                                                );
                                                                leanh::lean_inc_ref_n(
                                                                    v_inst_1964_,
                                                                    2,
                                                                );
                                                                leanh::lean_inc_ref_n(
                                                                    v_inst_1963_,
                                                                    2,
                                                                );
                                                                leanh::lean_inc_ref_n(
                                                                    v_inst_1962_,
                                                                    2,
                                                                );
                                                                leanh::lean_inc_n(
                                                                    v_inst_1961_,
                                                                    2,
                                                                );
                                                                v___f_2019_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14 as *mut core::ffi::c_void, 11, 10);
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    0,
                                                                    v_toPure_1960_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    1,
                                                                    v_inst_1961_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    2,
                                                                    v_inst_1962_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    3,
                                                                    v_inst_1963_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    4,
                                                                    v_inst_1964_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    5,
                                                                    v_inst_1965_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    6,
                                                                    v_toVar_1966_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    7,
                                                                    v_asVar_1967_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    8,
                                                                    v_arg_1975_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    9,
                                                                    v_toBind_1968_,
                                                                );
                                                                v___f_2020_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    0,
                                                                    v_asTopVar_1969_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    1,
                                                                    v_e_1959_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    2,
                                                                    v_inst_1961_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    3,
                                                                    v_inst_1962_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    4,
                                                                    v_inst_1963_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    5,
                                                                    v_inst_1964_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    6,
                                                                    v_inst_1965_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    7,
                                                                    v_toVar_1966_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    8,
                                                                    v_asVar_1967_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    9,
                                                                    v_arg_1979_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    10,
                                                                    v_toBind_1968_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    11,
                                                                    v___f_2019_,
                                                                );
                                                                v___x_2021_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                v___x_2022_ =
                                                                    leanh::lean_apply_4(
                                                                        v_toBind_1968_,
                                                                        leanh::lean_box(0),
                                                                        leanh::lean_box(0),
                                                                        v___x_2021_,
                                                                        v___f_2020_,
                                                                    );
                                                                return v___x_2022_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_2001_);
                                                            leanh::lean_dec(
                                                                v_toTopVar_1958_,
                                                            );
                                                            v___x_2023_ =
                                                                l_Lean_Meta_Sym_getNatValue_x3f(
                                                                    v_arg_1975_,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v___x_2023_,
                                                            ) == 1
                                                            {
                                                                v_val_2024_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2023_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_val_2024_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_2023_,
                                                                    1,
                                                                );
                                                                v___f_2025_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17 as *mut core::ffi::c_void, 3, 2);
                                                                leanh::lean_closure_set(
                                                                    v___f_2025_,
                                                                    0,
                                                                    v_val_2024_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2025_,
                                                                    1,
                                                                    v_toPure_1960_,
                                                                );
                                                                leanh::lean_inc(
                                                                    v_toBind_1968_,
                                                                );
                                                                leanh::lean_inc_ref(
                                                                    v_inst_1965_,
                                                                );
                                                                leanh::lean_inc_ref(
                                                                    v_inst_1964_,
                                                                );
                                                                leanh::lean_inc_ref(
                                                                    v_inst_1963_,
                                                                );
                                                                leanh::lean_inc_ref(
                                                                    v_inst_1962_,
                                                                );
                                                                leanh::lean_inc(
                                                                    v_inst_1961_,
                                                                );
                                                                v___f_2026_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    0,
                                                                    v_asTopVar_1969_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    1,
                                                                    v_e_1959_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    2,
                                                                    v_inst_1961_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    3,
                                                                    v_inst_1962_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    4,
                                                                    v_inst_1963_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    5,
                                                                    v_inst_1964_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    6,
                                                                    v_inst_1965_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    7,
                                                                    v_toVar_1966_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    8,
                                                                    v_asVar_1967_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    9,
                                                                    v_arg_1979_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    10,
                                                                    v_toBind_1968_,
                                                                );
                                                                leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    11,
                                                                    v___f_2025_,
                                                                );
                                                                v___x_2027_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                v___x_2028_ =
                                                                    leanh::lean_apply_4(
                                                                        v_toBind_1968_,
                                                                        leanh::lean_box(0),
                                                                        leanh::lean_box(0),
                                                                        v___x_2027_,
                                                                        v___f_2026_,
                                                                    );
                                                                return v___x_2028_;
                                                            } else {
                                                                leanh::lean_dec(v___x_2023_);
                                                                leanh::lean_dec_ref(
                                                                    v_arg_1983_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_1979_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_toBind_1968_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_asVar_1967_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_toVar_1966_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_inst_1965_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_inst_1964_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_inst_1963_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_inst_1962_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_inst_1961_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_toPure_1960_,
                                                                );
                                                                v___x_2029_ =
                                                                    leanh::lean_apply_1(
                                                                        v_asTopVar_1969_,
                                                                        v_e_1959_,
                                                                    );
                                                                return v___x_2029_;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_1984_);
                                            leanh::lean_dec_ref(v_arg_1983_);
                                            leanh::lean_dec(v_toPure_1960_);
                                            leanh::lean_dec(v_toTopVar_1958_);
                                            leanh::lean_inc(v_toBind_1968_);
                                            leanh::lean_inc_ref(v_inst_1965_);
                                            leanh::lean_inc_ref(v_inst_1964_);
                                            leanh::lean_inc_ref(v_inst_1963_);
                                            leanh::lean_inc_ref(v_inst_1962_);
                                            leanh::lean_inc(v_inst_1961_);
                                            v___f_2030_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                0,
                                                v_asTopVar_1969_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                1,
                                                v_e_1959_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                2,
                                                v_inst_1961_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                3,
                                                v_inst_1962_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                4,
                                                v_inst_1963_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                5,
                                                v_inst_1964_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                6,
                                                v_inst_1965_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                7,
                                                v_toVar_1966_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                8,
                                                v_asVar_1967_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                9,
                                                v_arg_1975_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                10,
                                                v_toBind_1968_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_2030_,
                                                11,
                                                v___f_1970_,
                                            );
                                            v___x_2031_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(
                                                v_inst_1961_,
                                                v_inst_1962_,
                                                v_inst_1963_,
                                                v_inst_1964_,
                                                v_inst_1965_,
                                                v_arg_1979_,
                                            );
                                            v___x_2032_ = leanh::lean_apply_4(
                                                v_toBind_1968_,
                                                leanh::lean_box(0),
                                                leanh::lean_box(0),
                                                v___x_2031_,
                                                v___f_2030_,
                                            );
                                            return v___x_2032_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_1984_);
                                        leanh::lean_dec_ref(v_arg_1983_);
                                        leanh::lean_dec(v___f_1970_);
                                        leanh::lean_dec(v_asVar_1967_);
                                        leanh::lean_dec(v_toVar_1966_);
                                        leanh::lean_dec_ref(v_inst_1962_);
                                        v___f_2033_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed as *mut core::ffi::c_void, 6, 5);
                                        leanh::lean_closure_set(
                                            v___f_2033_,
                                            0,
                                            v_asTopVar_1969_,
                                        );
                                        leanh::lean_closure_set(v___f_2033_, 1, v_e_1959_);
                                        leanh::lean_closure_set(v___f_2033_, 2, v_arg_1975_);
                                        leanh::lean_closure_set(
                                            v___f_2033_,
                                            3,
                                            v_toPure_1960_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_2033_,
                                            4,
                                            v_toTopVar_1958_,
                                        );
                                        v___x_2034_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(
                                            v_inst_1961_,
                                            v_inst_1963_,
                                            v_inst_1964_,
                                            v_inst_1965_,
                                            v_arg_1979_,
                                        );
                                        v___x_2035_ = leanh::lean_apply_4(
                                            v_toBind_1968_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v___x_2034_,
                                            v___f_2033_,
                                        );
                                        return v___x_2035_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_1984_);
                                    leanh::lean_dec_ref(v_arg_1983_);
                                    leanh::lean_dec(v___f_1970_);
                                    leanh::lean_dec(v_asVar_1967_);
                                    leanh::lean_dec(v_toVar_1966_);
                                    leanh::lean_dec_ref(v_inst_1962_);
                                    v___f_2036_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed as *mut core::ffi::c_void, 6, 5);
                                    leanh::lean_closure_set(
                                        v___f_2036_,
                                        0,
                                        v_asTopVar_1969_,
                                    );
                                    leanh::lean_closure_set(v___f_2036_, 1, v_e_1959_);
                                    leanh::lean_closure_set(v___f_2036_, 2, v_arg_1975_);
                                    leanh::lean_closure_set(v___f_2036_, 3, v_toPure_1960_);
                                    leanh::lean_closure_set(
                                        v___f_2036_,
                                        4,
                                        v_toTopVar_1958_,
                                    );
                                    v___x_2037_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(
                                        v_inst_1961_,
                                        v_inst_1963_,
                                        v_inst_1964_,
                                        v_inst_1965_,
                                        v_arg_1979_,
                                    );
                                    v___x_2038_ = leanh::lean_apply_4(
                                        v_toBind_1968_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2037_,
                                        v___f_2036_,
                                    );
                                    return v___x_2038_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1984_);
                                leanh::lean_dec_ref(v_arg_1983_);
                                leanh::lean_dec_ref(v_arg_1975_);
                                leanh::lean_dec(v___f_1970_);
                                leanh::lean_dec(v_toBind_1968_);
                                leanh::lean_dec(v_asVar_1967_);
                                leanh::lean_dec(v_toVar_1966_);
                                leanh::lean_dec_ref(v_inst_1965_);
                                leanh::lean_dec_ref(v_inst_1964_);
                                leanh::lean_dec_ref(v_inst_1963_);
                                leanh::lean_dec_ref(v_inst_1962_);
                                leanh::lean_dec(v_inst_1961_);
                                leanh::lean_dec(v_toTopVar_1958_);
                                if leanh::lean_obj_tag(v_arg_1979_) == 9 {
                                    v_a_2039_ = leanh::lean_ctor_get(v_arg_1979_, 0);
                                    leanh::lean_inc_ref(v_a_2039_);
                                    leanh::lean_dec_ref_known(v_arg_1979_, 1);
                                    if leanh::lean_obj_tag(v_a_2039_) == 0 {
                                        leanh::lean_dec(v_asTopVar_1969_);
                                        leanh::lean_dec_ref(v_e_1959_);
                                        v_val_2040_ = leanh::lean_ctor_get(v_a_2039_, 0);
                                        v_isSharedCheck_2050_ =
                                            (!leanh::lean_is_exclusive(v_a_2039_)) as u8;
                                        if v_isSharedCheck_2050_ == 0 {
                                            v___x_2042_ = v_a_2039_;
                                            v_isShared_2043_ = v_isSharedCheck_2050_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_val_2040_);
                                            leanh::lean_dec(v_a_2039_);
                                            v___x_2042_ = leanh::lean_box(0);
                                            v_isShared_2043_ = v_isSharedCheck_2050_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_a_2039_);
                                        leanh::lean_dec(v_toPure_1960_);
                                        v___x_2051_ =
                                            leanh::lean_apply_1(v_asTopVar_1969_, v_e_1959_);
                                        return v___x_2051_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_1979_);
                                    leanh::lean_dec(v_toPure_1960_);
                                    v___x_2052_ =
                                        leanh::lean_apply_1(v_asTopVar_1969_, v_e_1959_);
                                    return v___x_2052_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2044_ = lean_nat_to_int(v_val_2040_);
                if v_isShared_2043_ == 0 {
                    leanh::lean_ctor_set(v___x_2042_, 0, v___x_2044_);
                    v___x_2046_ = v___x_2042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2044_);
                    v___x_2046_ = v_reuseFailAlloc_2049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2047_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                v___x_2048_ = leanh::lean_apply_2(
                    v_toPure_1960_,
                    leanh::lean_box(0),
                    v___x_2047_,
                );
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(
    mut v_inst_2053_: *mut leanh::LeanObject,
    mut v_inst_2054_: *mut leanh::LeanObject,
    mut v_inst_2055_: *mut leanh::LeanObject,
    mut v_inst_2056_: *mut leanh::LeanObject,
    mut v_inst_2057_: *mut leanh::LeanObject,
    mut v_inst_2058_: *mut leanh::LeanObject,
    mut v_inst_2059_: *mut leanh::LeanObject,
    mut v_e_2060_: *mut leanh::LeanObject,
    mut v_skipVar_2061_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asVar_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toVar_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTopVar_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asTopVar_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2062_ = leanh::lean_ctor_get(v_inst_2056_, 0);
    v_toBind_2063_ = leanh::lean_ctor_get(v_inst_2056_, 1);
    leanh::lean_inc_n(v_toBind_2063_, 6);
    v_toPure_2064_ = leanh::lean_ctor_get(v_toApplicative_2062_, 1);
    leanh::lean_inc_n(v_toPure_2064_, 5);
    v___f_2065_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2065_, 0, v_toPure_2064_);
    v___f_2066_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2066_, 0, v_toPure_2064_);
    v___f_2067_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2067_, 0, v_toPure_2064_);
    leanh::lean_inc(v_inst_2053_);
    leanh::lean_inc_ref(v___f_2067_);
    leanh::lean_inc(v_inst_2059_);
    v_asVar_2068_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v_asVar_2068_, 0, v_inst_2059_);
    leanh::lean_closure_set(v_asVar_2068_, 1, v_toBind_2063_);
    leanh::lean_closure_set(v_asVar_2068_, 2, v___f_2067_);
    leanh::lean_closure_set(v_asVar_2068_, 3, v_inst_2053_);
    v_toVar_2069_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v_toVar_2069_, 0, v_inst_2059_);
    leanh::lean_closure_set(v_toVar_2069_, 1, v_toBind_2063_);
    leanh::lean_closure_set(v_toVar_2069_, 2, v___f_2067_);
    v___x_2070_ = leanh::lean_box((v_skipVar_2061_) as usize);
    leanh::lean_inc_ref(v_toVar_2069_);
    v_toTopVar_2071_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v_toTopVar_2071_, 0, v___x_2070_);
    leanh::lean_closure_set(v_toTopVar_2071_, 1, v_toVar_2069_);
    leanh::lean_closure_set(v_toTopVar_2071_, 2, v_toBind_2063_);
    leanh::lean_closure_set(v_toTopVar_2071_, 3, v___f_2066_);
    leanh::lean_closure_set(v_toTopVar_2071_, 4, v_toPure_2064_);
    leanh::lean_inc_ref(v_toTopVar_2071_);
    v_asTopVar_2072_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v_asTopVar_2072_, 0, v_toTopVar_2071_);
    leanh::lean_closure_set(v_asTopVar_2072_, 1, v_inst_2053_);
    leanh::lean_closure_set(v_asTopVar_2072_, 2, v_toBind_2063_);
    leanh::lean_inc(v_inst_2054_);
    leanh::lean_inc_ref(v_e_2060_);
    v___f_2073_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_2073_, 0, v_toTopVar_2071_);
    leanh::lean_closure_set(v___f_2073_, 1, v_e_2060_);
    leanh::lean_closure_set(v___f_2073_, 2, v_toPure_2064_);
    leanh::lean_closure_set(v___f_2073_, 3, v_inst_2054_);
    leanh::lean_closure_set(v___f_2073_, 4, v_inst_2055_);
    leanh::lean_closure_set(v___f_2073_, 5, v_inst_2056_);
    leanh::lean_closure_set(v___f_2073_, 6, v_inst_2057_);
    leanh::lean_closure_set(v___f_2073_, 7, v_inst_2058_);
    leanh::lean_closure_set(v___f_2073_, 8, v_toVar_2069_);
    leanh::lean_closure_set(v___f_2073_, 9, v_asVar_2068_);
    leanh::lean_closure_set(v___f_2073_, 10, v_toBind_2063_);
    leanh::lean_closure_set(v___f_2073_, 11, v_asTopVar_2072_);
    leanh::lean_closure_set(v___f_2073_, 12, v___f_2065_);
    v___x_2074_ = leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_2074_, 0, v_e_2060_);
    v___x_2075_ = leanh::lean_apply_2(v_inst_2054_, leanh::lean_box(0), v___x_2074_);
    v___x_2076_ = leanh::lean_apply_4(
        v_toBind_2063_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2075_,
        v___f_2073_,
    );
    return v___x_2076_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(
    mut v_inst_2077_: *mut leanh::LeanObject,
    mut v_inst_2078_: *mut leanh::LeanObject,
    mut v_inst_2079_: *mut leanh::LeanObject,
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_inst_2081_: *mut leanh::LeanObject,
    mut v_inst_2082_: *mut leanh::LeanObject,
    mut v_inst_2083_: *mut leanh::LeanObject,
    mut v_e_2084_: *mut leanh::LeanObject,
    mut v_skipVar_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipVar_boxed_2086_: u8 = 0;
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_2086_ = (leanh::lean_unbox(v_skipVar_2085_) as u8);
    v_res_2087_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(
        v_inst_2077_,
        v_inst_2078_,
        v_inst_2079_,
        v_inst_2080_,
        v_inst_2081_,
        v_inst_2082_,
        v_inst_2083_,
        v_e_2084_,
        v_skipVar_boxed_2086_,
    );
    return v_res_2087_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f(
    mut v_m_2088_: *mut leanh::LeanObject,
    mut v_inst_2089_: *mut leanh::LeanObject,
    mut v_inst_2090_: *mut leanh::LeanObject,
    mut v_inst_2091_: *mut leanh::LeanObject,
    mut v_inst_2092_: *mut leanh::LeanObject,
    mut v_inst_2093_: *mut leanh::LeanObject,
    mut v_inst_2094_: *mut leanh::LeanObject,
    mut v_inst_2095_: *mut leanh::LeanObject,
    mut v_e_2096_: *mut leanh::LeanObject,
    mut v_skipVar_2097_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(
        v_inst_2089_,
        v_inst_2090_,
        v_inst_2091_,
        v_inst_2092_,
        v_inst_2093_,
        v_inst_2094_,
        v_inst_2095_,
        v_e_2096_,
        v_skipVar_2097_,
    );
    return v___x_2098_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___boxed(
    mut v_m_2099_: *mut leanh::LeanObject,
    mut v_inst_2100_: *mut leanh::LeanObject,
    mut v_inst_2101_: *mut leanh::LeanObject,
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_inst_2103_: *mut leanh::LeanObject,
    mut v_inst_2104_: *mut leanh::LeanObject,
    mut v_inst_2105_: *mut leanh::LeanObject,
    mut v_inst_2106_: *mut leanh::LeanObject,
    mut v_e_2107_: *mut leanh::LeanObject,
    mut v_skipVar_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipVar_boxed_2109_: u8 = 0;
    let mut v_res_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_2109_ = (leanh::lean_unbox(v_skipVar_2108_) as u8);
    v_res_2110_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f(
        v_m_2099_,
        v_inst_2100_,
        v_inst_2101_,
        v_inst_2102_,
        v_inst_2103_,
        v_inst_2104_,
        v_inst_2105_,
        v_inst_2106_,
        v_e_2107_,
        v_skipVar_boxed_2109_,
    );
    return v_res_2110_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0;
    v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
    return v___x_2113_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(
    mut v_inst_2114_: *mut leanh::LeanObject,
    mut v_e_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1);
    v___x_2117_ = l_Lean_indentExpr(v_e_2115_);
    v___x_2118_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2118_, 0, v___x_2116_);
    leanh::lean_ctor_set(v___x_2118_, 1, v___x_2117_);
    v___x_2119_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_reportIssueIfVerbose___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    leanh::lean_closure_set(v___x_2119_, 0, v___x_2118_);
    v___x_2120_ = leanh::lean_apply_2(v_inst_2114_, leanh::lean_box(0), v___x_2119_);
    return v___x_2120_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(
    mut v_m_2121_: *mut leanh::LeanObject,
    mut v_inst_2122_: *mut leanh::LeanObject,
    mut v_e_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_2122_, v_e_2123_);
    return v___x_2124_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(
    mut v_arg_2125_: *mut leanh::LeanObject,
    mut v_asVar_2126_: *mut leanh::LeanObject,
    mut v_e_2127_: *mut leanh::LeanObject,
    mut v_arg_2128_: *mut leanh::LeanObject,
    mut v_toPure_2129_: *mut leanh::LeanObject,
    mut v_toVar_2130_: *mut leanh::LeanObject,
    mut v_____do__lift_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2145_: u8 = 0;
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2132_ = l_Lean_Expr_appArg_x21(v_____do__lift_2131_);
                v___x_2133_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_2132_,
                        v_arg_2125_,
                    );
                leanh::lean_dec_ref(v___x_2132_);
                if v___x_2133_ == 0 {
                    leanh::lean_dec(v_toVar_2130_);
                    leanh::lean_dec(v_toPure_2129_);
                    leanh::lean_dec_ref(v_arg_2128_);
                    v___x_2134_ = leanh::lean_apply_1(v_asVar_2126_, v_e_2127_);
                    return v___x_2134_;
                } else {
                    leanh::lean_dec(v_asVar_2126_);
                    v___x_2135_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2128_);
                    if leanh::lean_obj_tag(v___x_2135_) == 1 {
                        leanh::lean_dec(v_toVar_2130_);
                        leanh::lean_dec_ref(v_e_2127_);
                        v_val_2136_ = leanh::lean_ctor_get(v___x_2135_, 0);
                        v_isSharedCheck_2145_ =
                            (!leanh::lean_is_exclusive(v___x_2135_)) as u8;
                        if v_isSharedCheck_2145_ == 0 {
                            v___x_2138_ = v___x_2135_;
                            v_isShared_2139_ = v_isSharedCheck_2145_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2136_);
                            leanh::lean_dec(v___x_2135_);
                            v___x_2138_ = leanh::lean_box(0);
                            v_isShared_2139_ = v_isSharedCheck_2145_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2135_);
                        leanh::lean_dec(v_toPure_2129_);
                        v___x_2146_ = leanh::lean_apply_1(v_toVar_2130_, v_e_2127_);
                        return v___x_2146_;
                    }
                }
            }
            1 => {
                v___x_2140_ = lean_nat_to_int(v_val_2136_);
                if v_isShared_2139_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2138_, 0);
                    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2140_);
                    v___x_2142_ = v___x_2138_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2140_);
                    v___x_2142_ = v_reuseFailAlloc_2144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2143_ = leanh::lean_apply_2(
                    v_toPure_2129_,
                    leanh::lean_box(0),
                    v___x_2142_,
                );
                return v___x_2143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(
    mut v_arg_2147_: *mut leanh::LeanObject,
    mut v_asVar_2148_: *mut leanh::LeanObject,
    mut v_e_2149_: *mut leanh::LeanObject,
    mut v_arg_2150_: *mut leanh::LeanObject,
    mut v_toPure_2151_: *mut leanh::LeanObject,
    mut v_toVar_2152_: *mut leanh::LeanObject,
    mut v_____do__lift_2153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2154_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(v_arg_2147_, v_asVar_2148_, v_e_2149_, v_arg_2150_, v_toPure_2151_, v_toVar_2152_, v_____do__lift_2153_);
    leanh::lean_dec_ref(v_____do__lift_2153_);
    leanh::lean_dec_ref(v_arg_2147_);
    return v_res_2154_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(
    mut v_arg_2155_: *mut leanh::LeanObject,
    mut v_asVar_2156_: *mut leanh::LeanObject,
    mut v_e_2157_: *mut leanh::LeanObject,
    mut v_inst_2158_: *mut leanh::LeanObject,
    mut v_inst_2159_: *mut leanh::LeanObject,
    mut v_inst_2160_: *mut leanh::LeanObject,
    mut v_inst_2161_: *mut leanh::LeanObject,
    mut v_inst_2162_: *mut leanh::LeanObject,
    mut v_toVar_2163_: *mut leanh::LeanObject,
    mut v_arg_2164_: *mut leanh::LeanObject,
    mut v_toBind_2165_: *mut leanh::LeanObject,
    mut v___f_2166_: *mut leanh::LeanObject,
    mut v_____do__lift_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    v___x_2168_ = l_Lean_Expr_appArg_x21(v_____do__lift_2167_);
    v___x_2169_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2168_,
        v_arg_2155_,
    );
    leanh::lean_dec_ref(v___x_2168_);
    if v___x_2169_ == 0 {
        let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2166_);
        leanh::lean_dec(v_toBind_2165_);
        leanh::lean_dec_ref(v_arg_2164_);
        leanh::lean_dec(v_toVar_2163_);
        leanh::lean_dec_ref(v_inst_2162_);
        leanh::lean_dec_ref(v_inst_2161_);
        leanh::lean_dec_ref(v_inst_2160_);
        leanh::lean_dec_ref(v_inst_2159_);
        leanh::lean_dec(v_inst_2158_);
        v___x_2170_ = leanh::lean_apply_1(v_asVar_2156_, v_e_2157_);
        return v___x_2170_;
    } else {
        let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_2157_);
        v___x_2171_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_2158_, v_inst_2159_, v_inst_2160_, v_inst_2161_, v_inst_2162_, v_toVar_2163_, v_asVar_2156_, v_arg_2164_);
        v___x_2172_ = leanh::lean_apply_4(
            v_toBind_2165_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2171_,
            v___f_2166_,
        );
        return v___x_2172_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(
    mut v_arg_2173_: *mut leanh::LeanObject,
    mut v_asVar_2174_: *mut leanh::LeanObject,
    mut v_e_2175_: *mut leanh::LeanObject,
    mut v_inst_2176_: *mut leanh::LeanObject,
    mut v_inst_2177_: *mut leanh::LeanObject,
    mut v_inst_2178_: *mut leanh::LeanObject,
    mut v_inst_2179_: *mut leanh::LeanObject,
    mut v_inst_2180_: *mut leanh::LeanObject,
    mut v_toVar_2181_: *mut leanh::LeanObject,
    mut v_arg_2182_: *mut leanh::LeanObject,
    mut v_toBind_2183_: *mut leanh::LeanObject,
    mut v___f_2184_: *mut leanh::LeanObject,
    mut v_____do__lift_2185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2186_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(v_arg_2173_, v_asVar_2174_, v_e_2175_, v_inst_2176_, v_inst_2177_, v_inst_2178_, v_inst_2179_, v_inst_2180_, v_toVar_2181_, v_arg_2182_, v_toBind_2183_, v___f_2184_, v_____do__lift_2185_);
    leanh::lean_dec_ref(v_____do__lift_2185_);
    leanh::lean_dec_ref(v_arg_2173_);
    return v_res_2186_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(
    mut v_toPure_2187_: *mut leanh::LeanObject,
    mut v_inst_2188_: *mut leanh::LeanObject,
    mut v_inst_2189_: *mut leanh::LeanObject,
    mut v_inst_2190_: *mut leanh::LeanObject,
    mut v_inst_2191_: *mut leanh::LeanObject,
    mut v_inst_2192_: *mut leanh::LeanObject,
    mut v_toVar_2193_: *mut leanh::LeanObject,
    mut v_asVar_2194_: *mut leanh::LeanObject,
    mut v_arg_2195_: *mut leanh::LeanObject,
    mut v_toBind_2196_: *mut leanh::LeanObject,
    mut v_____do__lift_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2198_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_2198_, 0, v_____do__lift_2197_);
    leanh::lean_closure_set(v___f_2198_, 1, v_toPure_2187_);
    v___x_2199_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
            v_inst_2188_,
            v_inst_2189_,
            v_inst_2190_,
            v_inst_2191_,
            v_inst_2192_,
            v_toVar_2193_,
            v_asVar_2194_,
            v_arg_2195_,
        );
    v___x_2200_ = leanh::lean_apply_4(
        v_toBind_2196_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2199_,
        v___f_2198_,
    );
    return v___x_2200_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(
    mut v_toVar_2201_: *mut leanh::LeanObject,
    mut v_e_2202_: *mut leanh::LeanObject,
    mut v_toPure_2203_: *mut leanh::LeanObject,
    mut v_inst_2204_: *mut leanh::LeanObject,
    mut v_inst_2205_: *mut leanh::LeanObject,
    mut v_inst_2206_: *mut leanh::LeanObject,
    mut v_inst_2207_: *mut leanh::LeanObject,
    mut v_inst_2208_: *mut leanh::LeanObject,
    mut v_asVar_2209_: *mut leanh::LeanObject,
    mut v_toBind_2210_: *mut leanh::LeanObject,
    mut v_____x_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2273_: u8 = 0;
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2212_ = l_Lean_Expr_cleanupAnnotations(v_____x_2211_);
                v___x_2213_ = l_Lean_Expr_isApp(v___x_2212_);
                if v___x_2213_ == 0 {
                    leanh::lean_dec_ref(v___x_2212_);
                    leanh::lean_dec(v_toBind_2210_);
                    leanh::lean_dec(v_asVar_2209_);
                    leanh::lean_dec_ref(v_inst_2208_);
                    leanh::lean_dec_ref(v_inst_2207_);
                    leanh::lean_dec_ref(v_inst_2206_);
                    leanh::lean_dec_ref(v_inst_2205_);
                    leanh::lean_dec(v_inst_2204_);
                    leanh::lean_dec(v_toPure_2203_);
                    v___x_2214_ = leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                    return v___x_2214_;
                } else {
                    v_arg_2215_ = leanh::lean_ctor_get(v___x_2212_, 1);
                    leanh::lean_inc_ref(v_arg_2215_);
                    v___x_2216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2212_);
                    v___x_2217_ = l_Lean_Expr_isApp(v___x_2216_);
                    if v___x_2217_ == 0 {
                        leanh::lean_dec_ref(v___x_2216_);
                        leanh::lean_dec_ref(v_arg_2215_);
                        leanh::lean_dec(v_toBind_2210_);
                        leanh::lean_dec(v_asVar_2209_);
                        leanh::lean_dec_ref(v_inst_2208_);
                        leanh::lean_dec_ref(v_inst_2207_);
                        leanh::lean_dec_ref(v_inst_2206_);
                        leanh::lean_dec_ref(v_inst_2205_);
                        leanh::lean_dec(v_inst_2204_);
                        leanh::lean_dec(v_toPure_2203_);
                        v___x_2218_ = leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                        return v___x_2218_;
                    } else {
                        v_arg_2219_ = leanh::lean_ctor_get(v___x_2216_, 1);
                        leanh::lean_inc_ref(v_arg_2219_);
                        v___x_2220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2216_);
                        v___x_2221_ = l_Lean_Expr_isApp(v___x_2220_);
                        if v___x_2221_ == 0 {
                            leanh::lean_dec_ref(v___x_2220_);
                            leanh::lean_dec_ref(v_arg_2219_);
                            leanh::lean_dec_ref(v_arg_2215_);
                            leanh::lean_dec(v_toBind_2210_);
                            leanh::lean_dec(v_asVar_2209_);
                            leanh::lean_dec_ref(v_inst_2208_);
                            leanh::lean_dec_ref(v_inst_2207_);
                            leanh::lean_dec_ref(v_inst_2206_);
                            leanh::lean_dec_ref(v_inst_2205_);
                            leanh::lean_dec(v_inst_2204_);
                            leanh::lean_dec(v_toPure_2203_);
                            v___x_2222_ = leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                            return v___x_2222_;
                        } else {
                            v_arg_2223_ = leanh::lean_ctor_get(v___x_2220_, 1);
                            leanh::lean_inc_ref(v_arg_2223_);
                            v___x_2224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2220_);
                            v___x_2225_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4;
                            v___x_2226_ = l_Lean_Expr_isConstOf(v___x_2224_, v___x_2225_);
                            if v___x_2226_ == 0 {
                                v___x_2227_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7;
                                v___x_2228_ = l_Lean_Expr_isConstOf(v___x_2224_, v___x_2227_);
                                if v___x_2228_ == 0 {
                                    v___x_2229_ = l_Lean_Expr_isApp(v___x_2224_);
                                    if v___x_2229_ == 0 {
                                        leanh::lean_dec_ref(v___x_2224_);
                                        leanh::lean_dec_ref(v_arg_2223_);
                                        leanh::lean_dec_ref(v_arg_2219_);
                                        leanh::lean_dec_ref(v_arg_2215_);
                                        leanh::lean_dec(v_toBind_2210_);
                                        leanh::lean_dec(v_asVar_2209_);
                                        leanh::lean_dec_ref(v_inst_2208_);
                                        leanh::lean_dec_ref(v_inst_2207_);
                                        leanh::lean_dec_ref(v_inst_2206_);
                                        leanh::lean_dec_ref(v_inst_2205_);
                                        leanh::lean_dec(v_inst_2204_);
                                        leanh::lean_dec(v_toPure_2203_);
                                        v___x_2230_ =
                                            leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                                        return v___x_2230_;
                                    } else {
                                        v___x_2231_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2224_);
                                        v___x_2232_ = l_Lean_Expr_isApp(v___x_2231_);
                                        if v___x_2232_ == 0 {
                                            leanh::lean_dec_ref(v___x_2231_);
                                            leanh::lean_dec_ref(v_arg_2223_);
                                            leanh::lean_dec_ref(v_arg_2219_);
                                            leanh::lean_dec_ref(v_arg_2215_);
                                            leanh::lean_dec(v_toBind_2210_);
                                            leanh::lean_dec(v_asVar_2209_);
                                            leanh::lean_dec_ref(v_inst_2208_);
                                            leanh::lean_dec_ref(v_inst_2207_);
                                            leanh::lean_dec_ref(v_inst_2206_);
                                            leanh::lean_dec_ref(v_inst_2205_);
                                            leanh::lean_dec(v_inst_2204_);
                                            leanh::lean_dec(v_toPure_2203_);
                                            v___x_2233_ = leanh::lean_apply_1(
                                                v_toVar_2201_,
                                                v_e_2202_,
                                            );
                                            return v___x_2233_;
                                        } else {
                                            v___x_2234_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2231_);
                                            v___x_2235_ = l_Lean_Expr_isApp(v___x_2234_);
                                            if v___x_2235_ == 0 {
                                                leanh::lean_dec_ref(v___x_2234_);
                                                leanh::lean_dec_ref(v_arg_2223_);
                                                leanh::lean_dec_ref(v_arg_2219_);
                                                leanh::lean_dec_ref(v_arg_2215_);
                                                leanh::lean_dec(v_toBind_2210_);
                                                leanh::lean_dec(v_asVar_2209_);
                                                leanh::lean_dec_ref(v_inst_2208_);
                                                leanh::lean_dec_ref(v_inst_2207_);
                                                leanh::lean_dec_ref(v_inst_2206_);
                                                leanh::lean_dec_ref(v_inst_2205_);
                                                leanh::lean_dec(v_inst_2204_);
                                                leanh::lean_dec(v_toPure_2203_);
                                                v___x_2236_ = leanh::lean_apply_1(
                                                    v_toVar_2201_,
                                                    v_e_2202_,
                                                );
                                                return v___x_2236_;
                                            } else {
                                                v___x_2237_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_2234_);
                                                v___x_2238_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16;
                                                v___x_2239_ =
                                                    l_Lean_Expr_isConstOf(v___x_2237_, v___x_2238_);
                                                if v___x_2239_ == 0 {
                                                    v___x_2240_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22;
                                                    v___x_2241_ = l_Lean_Expr_isConstOf(
                                                        v___x_2237_,
                                                        v___x_2240_,
                                                    );
                                                    if v___x_2241_ == 0 {
                                                        v___x_2242_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25;
                                                        v___x_2243_ = l_Lean_Expr_isConstOf(
                                                            v___x_2237_,
                                                            v___x_2242_,
                                                        );
                                                        leanh::lean_dec_ref(v___x_2237_);
                                                        if v___x_2243_ == 0 {
                                                            leanh::lean_dec_ref(v_arg_2223_);
                                                            leanh::lean_dec_ref(v_arg_2219_);
                                                            leanh::lean_dec_ref(v_arg_2215_);
                                                            leanh::lean_dec(v_toBind_2210_);
                                                            leanh::lean_dec(v_asVar_2209_);
                                                            leanh::lean_dec_ref(
                                                                v_inst_2208_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_2207_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_2206_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_2205_,
                                                            );
                                                            leanh::lean_dec(v_inst_2204_);
                                                            leanh::lean_dec(v_toPure_2203_);
                                                            v___x_2244_ =
                                                                leanh::lean_apply_1(
                                                                    v_toVar_2201_,
                                                                    v_e_2202_,
                                                                );
                                                            return v___x_2244_;
                                                        } else {
                                                            leanh::lean_inc_n(
                                                                v_toBind_2210_,
                                                                2,
                                                            );
                                                            leanh::lean_inc(v_asVar_2209_);
                                                            leanh::lean_inc(v_toVar_2201_);
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2208_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2207_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2206_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2205_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_n(
                                                                v_inst_2204_,
                                                                2,
                                                            );
                                                            v___f_2245_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1 as *mut core::ffi::c_void, 11, 10);
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                0,
                                                                v_toPure_2203_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                1,
                                                                v_inst_2204_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                2,
                                                                v_inst_2205_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                3,
                                                                v_inst_2206_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                4,
                                                                v_inst_2207_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                5,
                                                                v_inst_2208_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                6,
                                                                v_toVar_2201_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                7,
                                                                v_asVar_2209_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                8,
                                                                v_arg_2215_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                9,
                                                                v_toBind_2210_,
                                                            );
                                                            v___f_2246_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                0,
                                                                v_arg_2223_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                1,
                                                                v_asVar_2209_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                2,
                                                                v_e_2202_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                3,
                                                                v_inst_2204_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                4,
                                                                v_inst_2205_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                5,
                                                                v_inst_2206_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                6,
                                                                v_inst_2207_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                7,
                                                                v_inst_2208_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                8,
                                                                v_toVar_2201_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                9,
                                                                v_arg_2219_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                10,
                                                                v_toBind_2210_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                11,
                                                                v___f_2245_,
                                                            );
                                                            v___x_2247_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_);
                                                            v___x_2248_ =
                                                                leanh::lean_apply_4(
                                                                    v_toBind_2210_,
                                                                    leanh::lean_box(0),
                                                                    leanh::lean_box(0),
                                                                    v___x_2247_,
                                                                    v___f_2246_,
                                                                );
                                                            return v___x_2248_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_2237_);
                                                        leanh::lean_inc_n(v_toBind_2210_, 2);
                                                        leanh::lean_inc(v_asVar_2209_);
                                                        leanh::lean_inc(v_toVar_2201_);
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2208_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2207_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2206_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2205_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_n(v_inst_2204_, 2);
                                                        v___f_2249_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3 as *mut core::ffi::c_void, 11, 10);
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            0,
                                                            v_toPure_2203_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            1,
                                                            v_inst_2204_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            2,
                                                            v_inst_2205_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            3,
                                                            v_inst_2206_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            4,
                                                            v_inst_2207_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            5,
                                                            v_inst_2208_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            6,
                                                            v_toVar_2201_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            7,
                                                            v_asVar_2209_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            8,
                                                            v_arg_2215_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            9,
                                                            v_toBind_2210_,
                                                        );
                                                        v___f_2250_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            0,
                                                            v_arg_2223_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            1,
                                                            v_asVar_2209_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            2,
                                                            v_e_2202_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            3,
                                                            v_inst_2204_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            4,
                                                            v_inst_2205_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            5,
                                                            v_inst_2206_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            6,
                                                            v_inst_2207_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            7,
                                                            v_inst_2208_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            8,
                                                            v_toVar_2201_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            9,
                                                            v_arg_2219_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            10,
                                                            v_toBind_2210_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            11,
                                                            v___f_2249_,
                                                        );
                                                        v___x_2251_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_);
                                                        v___x_2252_ = leanh::lean_apply_4(
                                                            v_toBind_2210_,
                                                            leanh::lean_box(0),
                                                            leanh::lean_box(0),
                                                            v___x_2251_,
                                                            v___f_2250_,
                                                        );
                                                        return v___x_2252_;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_2237_);
                                                    v___x_2253_ = l_Lean_Meta_Sym_getNatValue_x3f(
                                                        v_arg_2215_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_2253_) == 1
                                                    {
                                                        v_val_2254_ = leanh::lean_ctor_get(
                                                            v___x_2253_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_val_2254_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_2253_,
                                                            1,
                                                        );
                                                        v___f_2255_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9 as *mut core::ffi::c_void, 3, 2);
                                                        leanh::lean_closure_set(
                                                            v___f_2255_,
                                                            0,
                                                            v_val_2254_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2255_,
                                                            1,
                                                            v_toPure_2203_,
                                                        );
                                                        leanh::lean_inc(v_toBind_2210_);
                                                        leanh::lean_inc_ref(v_inst_2208_);
                                                        leanh::lean_inc_ref(v_inst_2207_);
                                                        leanh::lean_inc_ref(v_inst_2206_);
                                                        leanh::lean_inc_ref(v_inst_2205_);
                                                        leanh::lean_inc(v_inst_2204_);
                                                        v___f_2256_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            0,
                                                            v_arg_2223_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            1,
                                                            v_asVar_2209_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            2,
                                                            v_e_2202_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            3,
                                                            v_inst_2204_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            4,
                                                            v_inst_2205_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            5,
                                                            v_inst_2206_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            6,
                                                            v_inst_2207_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            7,
                                                            v_inst_2208_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            8,
                                                            v_toVar_2201_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            9,
                                                            v_arg_2219_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            10,
                                                            v_toBind_2210_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            11,
                                                            v___f_2255_,
                                                        );
                                                        v___x_2257_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_);
                                                        v___x_2258_ = leanh::lean_apply_4(
                                                            v_toBind_2210_,
                                                            leanh::lean_box(0),
                                                            leanh::lean_box(0),
                                                            v___x_2257_,
                                                            v___f_2256_,
                                                        );
                                                        return v___x_2258_;
                                                    } else {
                                                        leanh::lean_dec(v___x_2253_);
                                                        leanh::lean_dec_ref(v_arg_2223_);
                                                        leanh::lean_dec_ref(v_arg_2219_);
                                                        leanh::lean_dec(v_toBind_2210_);
                                                        leanh::lean_dec(v_asVar_2209_);
                                                        leanh::lean_dec_ref(v_inst_2208_);
                                                        leanh::lean_dec_ref(v_inst_2207_);
                                                        leanh::lean_dec_ref(v_inst_2206_);
                                                        leanh::lean_dec_ref(v_inst_2205_);
                                                        leanh::lean_dec(v_inst_2204_);
                                                        leanh::lean_dec(v_toPure_2203_);
                                                        v___x_2259_ = leanh::lean_apply_1(
                                                            v_toVar_2201_,
                                                            v_e_2202_,
                                                        );
                                                        return v___x_2259_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2224_);
                                    leanh::lean_dec_ref(v_arg_2223_);
                                    leanh::lean_dec_ref(v_inst_2205_);
                                    v___f_2260_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed as *mut core::ffi::c_void, 7, 6);
                                    leanh::lean_closure_set(v___f_2260_, 0, v_arg_2219_);
                                    leanh::lean_closure_set(v___f_2260_, 1, v_asVar_2209_);
                                    leanh::lean_closure_set(v___f_2260_, 2, v_e_2202_);
                                    leanh::lean_closure_set(v___f_2260_, 3, v_arg_2215_);
                                    leanh::lean_closure_set(v___f_2260_, 4, v_toPure_2203_);
                                    leanh::lean_closure_set(v___f_2260_, 5, v_toVar_2201_);
                                    v___x_2261_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
                                        v_inst_2204_,
                                        v_inst_2206_,
                                        v_inst_2207_,
                                        v_inst_2208_,
                                    );
                                    v___x_2262_ = leanh::lean_apply_4(
                                        v_toBind_2210_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2261_,
                                        v___f_2260_,
                                    );
                                    return v___x_2262_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_2224_);
                                leanh::lean_dec_ref(v_arg_2223_);
                                leanh::lean_dec_ref(v_arg_2215_);
                                leanh::lean_dec(v_toBind_2210_);
                                leanh::lean_dec(v_asVar_2209_);
                                leanh::lean_dec_ref(v_inst_2208_);
                                leanh::lean_dec_ref(v_inst_2207_);
                                leanh::lean_dec_ref(v_inst_2206_);
                                leanh::lean_dec_ref(v_inst_2205_);
                                leanh::lean_dec(v_inst_2204_);
                                if leanh::lean_obj_tag(v_arg_2219_) == 9 {
                                    v_a_2263_ = leanh::lean_ctor_get(v_arg_2219_, 0);
                                    leanh::lean_inc_ref(v_a_2263_);
                                    leanh::lean_dec_ref_known(v_arg_2219_, 1);
                                    if leanh::lean_obj_tag(v_a_2263_) == 0 {
                                        leanh::lean_dec_ref(v_e_2202_);
                                        leanh::lean_dec(v_toVar_2201_);
                                        v_val_2264_ = leanh::lean_ctor_get(v_a_2263_, 0);
                                        v_isSharedCheck_2273_ =
                                            (!leanh::lean_is_exclusive(v_a_2263_)) as u8;
                                        if v_isSharedCheck_2273_ == 0 {
                                            v___x_2266_ = v_a_2263_;
                                            v_isShared_2267_ = v_isSharedCheck_2273_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_val_2264_);
                                            leanh::lean_dec(v_a_2263_);
                                            v___x_2266_ = leanh::lean_box(0);
                                            v_isShared_2267_ = v_isSharedCheck_2273_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_a_2263_);
                                        leanh::lean_dec(v_toPure_2203_);
                                        v___x_2274_ =
                                            leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                                        return v___x_2274_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_2219_);
                                    leanh::lean_dec(v_toPure_2203_);
                                    v___x_2275_ =
                                        leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                                    return v___x_2275_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2268_ = lean_nat_to_int(v_val_2264_);
                if v_isShared_2267_ == 0 {
                    leanh::lean_ctor_set(v___x_2266_, 0, v___x_2268_);
                    v___x_2270_ = v___x_2266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2268_);
                    v___x_2270_ = v_reuseFailAlloc_2272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2271_ = leanh::lean_apply_2(
                    v_toPure_2203_,
                    leanh::lean_box(0),
                    v___x_2270_,
                );
                return v___x_2271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
    mut v_inst_2276_: *mut leanh::LeanObject,
    mut v_inst_2277_: *mut leanh::LeanObject,
    mut v_inst_2278_: *mut leanh::LeanObject,
    mut v_inst_2279_: *mut leanh::LeanObject,
    mut v_inst_2280_: *mut leanh::LeanObject,
    mut v_toVar_2281_: *mut leanh::LeanObject,
    mut v_asVar_2282_: *mut leanh::LeanObject,
    mut v_e_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2284_ = leanh::lean_ctor_get(v_inst_2278_, 0);
    v_toBind_2285_ = leanh::lean_ctor_get(v_inst_2278_, 1);
    leanh::lean_inc_n(v_toBind_2285_, 2);
    v_toPure_2286_ = leanh::lean_ctor_get(v_toApplicative_2284_, 1);
    leanh::lean_inc(v_toPure_2286_);
    leanh::lean_inc_ref(v_e_2283_);
    v___x_2287_ = leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_2287_, 0, v_e_2283_);
    leanh::lean_inc(v_inst_2276_);
    v___x_2288_ = leanh::lean_apply_2(v_inst_2276_, leanh::lean_box(0), v___x_2287_);
    v___f_2289_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2 as *mut core::ffi::c_void, 11, 10);
    leanh::lean_closure_set(v___f_2289_, 0, v_toVar_2281_);
    leanh::lean_closure_set(v___f_2289_, 1, v_e_2283_);
    leanh::lean_closure_set(v___f_2289_, 2, v_toPure_2286_);
    leanh::lean_closure_set(v___f_2289_, 3, v_inst_2276_);
    leanh::lean_closure_set(v___f_2289_, 4, v_inst_2277_);
    leanh::lean_closure_set(v___f_2289_, 5, v_inst_2278_);
    leanh::lean_closure_set(v___f_2289_, 6, v_inst_2279_);
    leanh::lean_closure_set(v___f_2289_, 7, v_inst_2280_);
    leanh::lean_closure_set(v___f_2289_, 8, v_asVar_2282_);
    leanh::lean_closure_set(v___f_2289_, 9, v_toBind_2285_);
    v___x_2290_ = leanh::lean_apply_4(
        v_toBind_2285_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2288_,
        v___f_2289_,
    );
    return v___x_2290_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(
    mut v_toPure_2291_: *mut leanh::LeanObject,
    mut v_inst_2292_: *mut leanh::LeanObject,
    mut v_inst_2293_: *mut leanh::LeanObject,
    mut v_inst_2294_: *mut leanh::LeanObject,
    mut v_inst_2295_: *mut leanh::LeanObject,
    mut v_inst_2296_: *mut leanh::LeanObject,
    mut v_toVar_2297_: *mut leanh::LeanObject,
    mut v_asVar_2298_: *mut leanh::LeanObject,
    mut v_arg_2299_: *mut leanh::LeanObject,
    mut v_toBind_2300_: *mut leanh::LeanObject,
    mut v_____do__lift_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2302_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_2302_, 0, v_____do__lift_2301_);
    leanh::lean_closure_set(v___f_2302_, 1, v_toPure_2291_);
    v___x_2303_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
            v_inst_2292_,
            v_inst_2293_,
            v_inst_2294_,
            v_inst_2295_,
            v_inst_2296_,
            v_toVar_2297_,
            v_asVar_2298_,
            v_arg_2299_,
        );
    v___x_2304_ = leanh::lean_apply_4(
        v_toBind_2300_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2303_,
        v___f_2302_,
    );
    return v___x_2304_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(
    mut v_m_2305_: *mut leanh::LeanObject,
    mut v_inst_2306_: *mut leanh::LeanObject,
    mut v_inst_2307_: *mut leanh::LeanObject,
    mut v_inst_2308_: *mut leanh::LeanObject,
    mut v_inst_2309_: *mut leanh::LeanObject,
    mut v_inst_2310_: *mut leanh::LeanObject,
    mut v_toVar_2311_: *mut leanh::LeanObject,
    mut v_asVar_2312_: *mut leanh::LeanObject,
    mut v_e_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
            v_inst_2306_,
            v_inst_2307_,
            v_inst_2308_,
            v_inst_2309_,
            v_inst_2310_,
            v_toVar_2311_,
            v_asVar_2312_,
            v_e_2313_,
        );
    return v___x_2314_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3(
    mut v_inst_2315_: *mut leanh::LeanObject,
    mut v_toBind_2316_: *mut leanh::LeanObject,
    mut v___f_2317_: *mut leanh::LeanObject,
    mut v_inst_2318_: *mut leanh::LeanObject,
    mut v_e_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2316_);
    leanh::lean_inc_ref(v_e_2319_);
    v___f_2320_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2320_, 0, v_inst_2315_);
    leanh::lean_closure_set(v___f_2320_, 1, v_e_2319_);
    leanh::lean_closure_set(v___f_2320_, 2, v_toBind_2316_);
    leanh::lean_closure_set(v___f_2320_, 3, v___f_2317_);
    v___x_2321_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_2318_, v_e_2319_);
    v___x_2322_ = leanh::lean_apply_4(
        v_toBind_2316_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2321_,
        v___f_2320_,
    );
    return v___x_2322_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(
    mut v_toVar_2323_: *mut leanh::LeanObject,
    mut v_toBind_2324_: *mut leanh::LeanObject,
    mut v___f_2325_: *mut leanh::LeanObject,
    mut v_e_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = leanh::lean_apply_1(v_toVar_2323_, v_e_2326_);
    v___x_2328_ = leanh::lean_apply_4(
        v_toBind_2324_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2327_,
        v___f_2325_,
    );
    return v___x_2328_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(
    mut v_toTopVar_2329_: *mut leanh::LeanObject,
    mut v_inst_2330_: *mut leanh::LeanObject,
    mut v_toBind_2331_: *mut leanh::LeanObject,
    mut v_e_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_e_2332_);
    v___f_2333_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2333_, 0, v_toTopVar_2329_);
    leanh::lean_closure_set(v___f_2333_, 1, v_e_2332_);
    v___x_2334_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_2330_, v_e_2332_);
    v___x_2335_ = leanh::lean_apply_4(
        v_toBind_2331_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2334_,
        v___f_2333_,
    );
    return v___x_2335_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(
    mut v_toPure_2336_: *mut leanh::LeanObject,
    mut v_inst_2337_: *mut leanh::LeanObject,
    mut v_inst_2338_: *mut leanh::LeanObject,
    mut v_inst_2339_: *mut leanh::LeanObject,
    mut v_inst_2340_: *mut leanh::LeanObject,
    mut v_inst_2341_: *mut leanh::LeanObject,
    mut v_toVar_2342_: *mut leanh::LeanObject,
    mut v_asVar_2343_: *mut leanh::LeanObject,
    mut v_arg_2344_: *mut leanh::LeanObject,
    mut v_toBind_2345_: *mut leanh::LeanObject,
    mut v_____do__lift_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2347_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2347_, 0, v_____do__lift_2346_);
    leanh::lean_closure_set(v___f_2347_, 1, v_toPure_2336_);
    v___x_2348_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
            v_inst_2337_,
            v_inst_2338_,
            v_inst_2339_,
            v_inst_2340_,
            v_inst_2341_,
            v_toVar_2342_,
            v_asVar_2343_,
            v_arg_2344_,
        );
    v___x_2349_ = leanh::lean_apply_4(
        v_toBind_2345_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2348_,
        v___f_2347_,
    );
    return v___x_2349_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(
    mut v_arg_2350_: *mut leanh::LeanObject,
    mut v_asTopVar_2351_: *mut leanh::LeanObject,
    mut v_e_2352_: *mut leanh::LeanObject,
    mut v_inst_2353_: *mut leanh::LeanObject,
    mut v_inst_2354_: *mut leanh::LeanObject,
    mut v_inst_2355_: *mut leanh::LeanObject,
    mut v_inst_2356_: *mut leanh::LeanObject,
    mut v_inst_2357_: *mut leanh::LeanObject,
    mut v_toVar_2358_: *mut leanh::LeanObject,
    mut v_asVar_2359_: *mut leanh::LeanObject,
    mut v_arg_2360_: *mut leanh::LeanObject,
    mut v_toBind_2361_: *mut leanh::LeanObject,
    mut v___f_2362_: *mut leanh::LeanObject,
    mut v_____do__lift_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    v___x_2364_ = l_Lean_Expr_appArg_x21(v_____do__lift_2363_);
    v___x_2365_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2364_,
        v_arg_2350_,
    );
    leanh::lean_dec_ref(v___x_2364_);
    if v___x_2365_ == 0 {
        let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2362_);
        leanh::lean_dec(v_toBind_2361_);
        leanh::lean_dec_ref(v_arg_2360_);
        leanh::lean_dec(v_asVar_2359_);
        leanh::lean_dec(v_toVar_2358_);
        leanh::lean_dec_ref(v_inst_2357_);
        leanh::lean_dec_ref(v_inst_2356_);
        leanh::lean_dec_ref(v_inst_2355_);
        leanh::lean_dec_ref(v_inst_2354_);
        leanh::lean_dec(v_inst_2353_);
        v___x_2366_ = leanh::lean_apply_1(v_asTopVar_2351_, v_e_2352_);
        return v___x_2366_;
    } else {
        let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_2352_);
        leanh::lean_dec(v_asTopVar_2351_);
        v___x_2367_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_2353_, v_inst_2354_, v_inst_2355_, v_inst_2356_, v_inst_2357_, v_toVar_2358_, v_asVar_2359_, v_arg_2360_);
        v___x_2368_ = leanh::lean_apply_4(
            v_toBind_2361_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2367_,
            v___f_2362_,
        );
        return v___x_2368_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(
    mut v_arg_2369_: *mut leanh::LeanObject,
    mut v_asTopVar_2370_: *mut leanh::LeanObject,
    mut v_e_2371_: *mut leanh::LeanObject,
    mut v_inst_2372_: *mut leanh::LeanObject,
    mut v_inst_2373_: *mut leanh::LeanObject,
    mut v_inst_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
    mut v_inst_2376_: *mut leanh::LeanObject,
    mut v_toVar_2377_: *mut leanh::LeanObject,
    mut v_asVar_2378_: *mut leanh::LeanObject,
    mut v_arg_2379_: *mut leanh::LeanObject,
    mut v_toBind_2380_: *mut leanh::LeanObject,
    mut v___f_2381_: *mut leanh::LeanObject,
    mut v_____do__lift_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(
        v_arg_2369_,
        v_asTopVar_2370_,
        v_e_2371_,
        v_inst_2372_,
        v_inst_2373_,
        v_inst_2374_,
        v_inst_2375_,
        v_inst_2376_,
        v_toVar_2377_,
        v_asVar_2378_,
        v_arg_2379_,
        v_toBind_2380_,
        v___f_2381_,
        v_____do__lift_2382_,
    );
    leanh::lean_dec_ref(v_____do__lift_2382_);
    leanh::lean_dec_ref(v_arg_2369_);
    return v_res_2383_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(
    mut v_toPure_2384_: *mut leanh::LeanObject,
    mut v_inst_2385_: *mut leanh::LeanObject,
    mut v_inst_2386_: *mut leanh::LeanObject,
    mut v_inst_2387_: *mut leanh::LeanObject,
    mut v_inst_2388_: *mut leanh::LeanObject,
    mut v_inst_2389_: *mut leanh::LeanObject,
    mut v_toVar_2390_: *mut leanh::LeanObject,
    mut v_asVar_2391_: *mut leanh::LeanObject,
    mut v_arg_2392_: *mut leanh::LeanObject,
    mut v_toBind_2393_: *mut leanh::LeanObject,
    mut v_____do__lift_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2395_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2395_, 0, v_____do__lift_2394_);
    leanh::lean_closure_set(v___f_2395_, 1, v_toPure_2384_);
    v___x_2396_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
            v_inst_2385_,
            v_inst_2386_,
            v_inst_2387_,
            v_inst_2388_,
            v_inst_2389_,
            v_toVar_2390_,
            v_asVar_2391_,
            v_arg_2392_,
        );
    v___x_2397_ = leanh::lean_apply_4(
        v_toBind_2393_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2396_,
        v___f_2395_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(
    mut v_arg_2398_: *mut leanh::LeanObject,
    mut v_asTopVar_2399_: *mut leanh::LeanObject,
    mut v_e_2400_: *mut leanh::LeanObject,
    mut v_arg_2401_: *mut leanh::LeanObject,
    mut v_toPure_2402_: *mut leanh::LeanObject,
    mut v_toTopVar_2403_: *mut leanh::LeanObject,
    mut v_____do__lift_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2405_ = l_Lean_Expr_appArg_x21(v_____do__lift_2404_);
                v___x_2406_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_2405_,
                        v_arg_2398_,
                    );
                leanh::lean_dec_ref(v___x_2405_);
                if v___x_2406_ == 0 {
                    leanh::lean_dec(v_toTopVar_2403_);
                    leanh::lean_dec(v_toPure_2402_);
                    leanh::lean_dec_ref(v_arg_2401_);
                    v___x_2407_ = leanh::lean_apply_1(v_asTopVar_2399_, v_e_2400_);
                    return v___x_2407_;
                } else {
                    leanh::lean_dec(v_asTopVar_2399_);
                    v___x_2408_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2401_);
                    if leanh::lean_obj_tag(v___x_2408_) == 1 {
                        leanh::lean_dec(v_toTopVar_2403_);
                        leanh::lean_dec_ref(v_e_2400_);
                        v_val_2409_ = leanh::lean_ctor_get(v___x_2408_, 0);
                        v_isSharedCheck_2419_ =
                            (!leanh::lean_is_exclusive(v___x_2408_)) as u8;
                        if v_isSharedCheck_2419_ == 0 {
                            v___x_2411_ = v___x_2408_;
                            v_isShared_2412_ = v_isSharedCheck_2419_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2409_);
                            leanh::lean_dec(v___x_2408_);
                            v___x_2411_ = leanh::lean_box(0);
                            v_isShared_2412_ = v_isSharedCheck_2419_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2408_);
                        leanh::lean_dec(v_toPure_2402_);
                        v___x_2420_ = leanh::lean_apply_1(v_toTopVar_2403_, v_e_2400_);
                        return v___x_2420_;
                    }
                }
            }
            1 => {
                v___x_2413_ = lean_nat_to_int(v_val_2409_);
                v___x_2414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                if v_isShared_2412_ == 0 {
                    leanh::lean_ctor_set(v___x_2411_, 0, v___x_2414_);
                    v___x_2416_ = v___x_2411_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2414_);
                    v___x_2416_ = v_reuseFailAlloc_2418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2417_ = leanh::lean_apply_2(
                    v_toPure_2402_,
                    leanh::lean_box(0),
                    v___x_2416_,
                );
                return v___x_2417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(
    mut v_arg_2421_: *mut leanh::LeanObject,
    mut v_asTopVar_2422_: *mut leanh::LeanObject,
    mut v_e_2423_: *mut leanh::LeanObject,
    mut v_arg_2424_: *mut leanh::LeanObject,
    mut v_toPure_2425_: *mut leanh::LeanObject,
    mut v_toTopVar_2426_: *mut leanh::LeanObject,
    mut v_____do__lift_2427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2428_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(
        v_arg_2421_,
        v_asTopVar_2422_,
        v_e_2423_,
        v_arg_2424_,
        v_toPure_2425_,
        v_toTopVar_2426_,
        v_____do__lift_2427_,
    );
    leanh::lean_dec_ref(v_____do__lift_2427_);
    leanh::lean_dec_ref(v_arg_2421_);
    return v_res_2428_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(
    mut v_toTopVar_2429_: *mut leanh::LeanObject,
    mut v_e_2430_: *mut leanh::LeanObject,
    mut v_toPure_2431_: *mut leanh::LeanObject,
    mut v_inst_2432_: *mut leanh::LeanObject,
    mut v_inst_2433_: *mut leanh::LeanObject,
    mut v_inst_2434_: *mut leanh::LeanObject,
    mut v_inst_2435_: *mut leanh::LeanObject,
    mut v_inst_2436_: *mut leanh::LeanObject,
    mut v_toVar_2437_: *mut leanh::LeanObject,
    mut v_asVar_2438_: *mut leanh::LeanObject,
    mut v_toBind_2439_: *mut leanh::LeanObject,
    mut v_asTopVar_2440_: *mut leanh::LeanObject,
    mut v_____x_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: u8 = 0;
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u8 = 0;
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2442_ = l_Lean_Expr_cleanupAnnotations(v_____x_2441_);
                v___x_2443_ = l_Lean_Expr_isApp(v___x_2442_);
                if v___x_2443_ == 0 {
                    leanh::lean_dec_ref(v___x_2442_);
                    leanh::lean_dec(v_asTopVar_2440_);
                    leanh::lean_dec(v_toBind_2439_);
                    leanh::lean_dec(v_asVar_2438_);
                    leanh::lean_dec(v_toVar_2437_);
                    leanh::lean_dec_ref(v_inst_2436_);
                    leanh::lean_dec_ref(v_inst_2435_);
                    leanh::lean_dec_ref(v_inst_2434_);
                    leanh::lean_dec_ref(v_inst_2433_);
                    leanh::lean_dec(v_inst_2432_);
                    leanh::lean_dec(v_toPure_2431_);
                    v___x_2444_ = leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                    return v___x_2444_;
                } else {
                    v_arg_2445_ = leanh::lean_ctor_get(v___x_2442_, 1);
                    leanh::lean_inc_ref(v_arg_2445_);
                    v___x_2446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2442_);
                    v___x_2447_ = l_Lean_Expr_isApp(v___x_2446_);
                    if v___x_2447_ == 0 {
                        leanh::lean_dec_ref(v___x_2446_);
                        leanh::lean_dec_ref(v_arg_2445_);
                        leanh::lean_dec(v_asTopVar_2440_);
                        leanh::lean_dec(v_toBind_2439_);
                        leanh::lean_dec(v_asVar_2438_);
                        leanh::lean_dec(v_toVar_2437_);
                        leanh::lean_dec_ref(v_inst_2436_);
                        leanh::lean_dec_ref(v_inst_2435_);
                        leanh::lean_dec_ref(v_inst_2434_);
                        leanh::lean_dec_ref(v_inst_2433_);
                        leanh::lean_dec(v_inst_2432_);
                        leanh::lean_dec(v_toPure_2431_);
                        v___x_2448_ = leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                        return v___x_2448_;
                    } else {
                        v_arg_2449_ = leanh::lean_ctor_get(v___x_2446_, 1);
                        leanh::lean_inc_ref(v_arg_2449_);
                        v___x_2450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2446_);
                        v___x_2451_ = l_Lean_Expr_isApp(v___x_2450_);
                        if v___x_2451_ == 0 {
                            leanh::lean_dec_ref(v___x_2450_);
                            leanh::lean_dec_ref(v_arg_2449_);
                            leanh::lean_dec_ref(v_arg_2445_);
                            leanh::lean_dec(v_asTopVar_2440_);
                            leanh::lean_dec(v_toBind_2439_);
                            leanh::lean_dec(v_asVar_2438_);
                            leanh::lean_dec(v_toVar_2437_);
                            leanh::lean_dec_ref(v_inst_2436_);
                            leanh::lean_dec_ref(v_inst_2435_);
                            leanh::lean_dec_ref(v_inst_2434_);
                            leanh::lean_dec_ref(v_inst_2433_);
                            leanh::lean_dec(v_inst_2432_);
                            leanh::lean_dec(v_toPure_2431_);
                            v___x_2452_ = leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                            return v___x_2452_;
                        } else {
                            v_arg_2453_ = leanh::lean_ctor_get(v___x_2450_, 1);
                            leanh::lean_inc_ref(v_arg_2453_);
                            v___x_2454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2450_);
                            v___x_2455_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4;
                            v___x_2456_ = l_Lean_Expr_isConstOf(v___x_2454_, v___x_2455_);
                            if v___x_2456_ == 0 {
                                v___x_2457_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7;
                                v___x_2458_ = l_Lean_Expr_isConstOf(v___x_2454_, v___x_2457_);
                                if v___x_2458_ == 0 {
                                    v___x_2459_ = l_Lean_Expr_isApp(v___x_2454_);
                                    if v___x_2459_ == 0 {
                                        leanh::lean_dec_ref(v___x_2454_);
                                        leanh::lean_dec_ref(v_arg_2453_);
                                        leanh::lean_dec_ref(v_arg_2449_);
                                        leanh::lean_dec_ref(v_arg_2445_);
                                        leanh::lean_dec(v_asTopVar_2440_);
                                        leanh::lean_dec(v_toBind_2439_);
                                        leanh::lean_dec(v_asVar_2438_);
                                        leanh::lean_dec(v_toVar_2437_);
                                        leanh::lean_dec_ref(v_inst_2436_);
                                        leanh::lean_dec_ref(v_inst_2435_);
                                        leanh::lean_dec_ref(v_inst_2434_);
                                        leanh::lean_dec_ref(v_inst_2433_);
                                        leanh::lean_dec(v_inst_2432_);
                                        leanh::lean_dec(v_toPure_2431_);
                                        v___x_2460_ =
                                            leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                                        return v___x_2460_;
                                    } else {
                                        v___x_2461_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2454_);
                                        v___x_2462_ = l_Lean_Expr_isApp(v___x_2461_);
                                        if v___x_2462_ == 0 {
                                            leanh::lean_dec_ref(v___x_2461_);
                                            leanh::lean_dec_ref(v_arg_2453_);
                                            leanh::lean_dec_ref(v_arg_2449_);
                                            leanh::lean_dec_ref(v_arg_2445_);
                                            leanh::lean_dec(v_asTopVar_2440_);
                                            leanh::lean_dec(v_toBind_2439_);
                                            leanh::lean_dec(v_asVar_2438_);
                                            leanh::lean_dec(v_toVar_2437_);
                                            leanh::lean_dec_ref(v_inst_2436_);
                                            leanh::lean_dec_ref(v_inst_2435_);
                                            leanh::lean_dec_ref(v_inst_2434_);
                                            leanh::lean_dec_ref(v_inst_2433_);
                                            leanh::lean_dec(v_inst_2432_);
                                            leanh::lean_dec(v_toPure_2431_);
                                            v___x_2463_ = leanh::lean_apply_1(
                                                v_toTopVar_2429_,
                                                v_e_2430_,
                                            );
                                            return v___x_2463_;
                                        } else {
                                            v___x_2464_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2461_);
                                            v___x_2465_ = l_Lean_Expr_isApp(v___x_2464_);
                                            if v___x_2465_ == 0 {
                                                leanh::lean_dec_ref(v___x_2464_);
                                                leanh::lean_dec_ref(v_arg_2453_);
                                                leanh::lean_dec_ref(v_arg_2449_);
                                                leanh::lean_dec_ref(v_arg_2445_);
                                                leanh::lean_dec(v_asTopVar_2440_);
                                                leanh::lean_dec(v_toBind_2439_);
                                                leanh::lean_dec(v_asVar_2438_);
                                                leanh::lean_dec(v_toVar_2437_);
                                                leanh::lean_dec_ref(v_inst_2436_);
                                                leanh::lean_dec_ref(v_inst_2435_);
                                                leanh::lean_dec_ref(v_inst_2434_);
                                                leanh::lean_dec_ref(v_inst_2433_);
                                                leanh::lean_dec(v_inst_2432_);
                                                leanh::lean_dec(v_toPure_2431_);
                                                v___x_2466_ = leanh::lean_apply_1(
                                                    v_toTopVar_2429_,
                                                    v_e_2430_,
                                                );
                                                return v___x_2466_;
                                            } else {
                                                v___x_2467_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_2464_);
                                                v___x_2468_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16;
                                                v___x_2469_ =
                                                    l_Lean_Expr_isConstOf(v___x_2467_, v___x_2468_);
                                                if v___x_2469_ == 0 {
                                                    v___x_2470_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22;
                                                    v___x_2471_ = l_Lean_Expr_isConstOf(
                                                        v___x_2467_,
                                                        v___x_2470_,
                                                    );
                                                    if v___x_2471_ == 0 {
                                                        v___x_2472_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25;
                                                        v___x_2473_ = l_Lean_Expr_isConstOf(
                                                            v___x_2467_,
                                                            v___x_2472_,
                                                        );
                                                        leanh::lean_dec_ref(v___x_2467_);
                                                        if v___x_2473_ == 0 {
                                                            leanh::lean_dec_ref(v_arg_2453_);
                                                            leanh::lean_dec_ref(v_arg_2449_);
                                                            leanh::lean_dec_ref(v_arg_2445_);
                                                            leanh::lean_dec(
                                                                v_asTopVar_2440_,
                                                            );
                                                            leanh::lean_dec(v_toBind_2439_);
                                                            leanh::lean_dec(v_asVar_2438_);
                                                            leanh::lean_dec(v_toVar_2437_);
                                                            leanh::lean_dec_ref(
                                                                v_inst_2436_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_2435_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_2434_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_inst_2433_,
                                                            );
                                                            leanh::lean_dec(v_inst_2432_);
                                                            leanh::lean_dec(v_toPure_2431_);
                                                            v___x_2474_ =
                                                                leanh::lean_apply_1(
                                                                    v_toTopVar_2429_,
                                                                    v_e_2430_,
                                                                );
                                                            return v___x_2474_;
                                                        } else {
                                                            leanh::lean_dec(
                                                                v_toTopVar_2429_,
                                                            );
                                                            leanh::lean_inc_n(
                                                                v_toBind_2439_,
                                                                2,
                                                            );
                                                            leanh::lean_inc(v_asVar_2438_);
                                                            leanh::lean_inc(v_toVar_2437_);
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2436_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2435_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2434_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_ref_n(
                                                                v_inst_2433_,
                                                                2,
                                                            );
                                                            leanh::lean_inc_n(
                                                                v_inst_2432_,
                                                                2,
                                                            );
                                                            v___f_2475_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4 as *mut core::ffi::c_void, 11, 10);
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                0,
                                                                v_toPure_2431_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                1,
                                                                v_inst_2432_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                2,
                                                                v_inst_2433_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                3,
                                                                v_inst_2434_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                4,
                                                                v_inst_2435_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                5,
                                                                v_inst_2436_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                6,
                                                                v_toVar_2437_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                7,
                                                                v_asVar_2438_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                8,
                                                                v_arg_2445_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                9,
                                                                v_toBind_2439_,
                                                            );
                                                            v___f_2476_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                0,
                                                                v_arg_2453_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                1,
                                                                v_asTopVar_2440_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                2,
                                                                v_e_2430_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                3,
                                                                v_inst_2432_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                4,
                                                                v_inst_2433_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                5,
                                                                v_inst_2434_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                6,
                                                                v_inst_2435_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                7,
                                                                v_inst_2436_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                8,
                                                                v_toVar_2437_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                9,
                                                                v_asVar_2438_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                10,
                                                                v_arg_2449_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                11,
                                                                v_toBind_2439_,
                                                            );
                                                            leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                12,
                                                                v___f_2475_,
                                                            );
                                                            v___x_2477_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_);
                                                            v___x_2478_ =
                                                                leanh::lean_apply_4(
                                                                    v_toBind_2439_,
                                                                    leanh::lean_box(0),
                                                                    leanh::lean_box(0),
                                                                    v___x_2477_,
                                                                    v___f_2476_,
                                                                );
                                                            return v___x_2478_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_2467_);
                                                        leanh::lean_dec(v_toTopVar_2429_);
                                                        leanh::lean_inc_n(v_toBind_2439_, 2);
                                                        leanh::lean_inc(v_asVar_2438_);
                                                        leanh::lean_inc(v_toVar_2437_);
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2436_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2435_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2434_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_ref_n(
                                                            v_inst_2433_,
                                                            2,
                                                        );
                                                        leanh::lean_inc_n(v_inst_2432_, 2);
                                                        v___f_2479_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            0,
                                                            v_toPure_2431_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            1,
                                                            v_inst_2432_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            2,
                                                            v_inst_2433_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            3,
                                                            v_inst_2434_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            4,
                                                            v_inst_2435_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            5,
                                                            v_inst_2436_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            6,
                                                            v_toVar_2437_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            7,
                                                            v_asVar_2438_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            8,
                                                            v_arg_2445_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            9,
                                                            v_toBind_2439_,
                                                        );
                                                        v___f_2480_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            0,
                                                            v_arg_2453_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            1,
                                                            v_asTopVar_2440_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            2,
                                                            v_e_2430_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            3,
                                                            v_inst_2432_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            4,
                                                            v_inst_2433_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            5,
                                                            v_inst_2434_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            6,
                                                            v_inst_2435_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            7,
                                                            v_inst_2436_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            8,
                                                            v_toVar_2437_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            9,
                                                            v_asVar_2438_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            10,
                                                            v_arg_2449_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            11,
                                                            v_toBind_2439_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            12,
                                                            v___f_2479_,
                                                        );
                                                        v___x_2481_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_);
                                                        v___x_2482_ = leanh::lean_apply_4(
                                                            v_toBind_2439_,
                                                            leanh::lean_box(0),
                                                            leanh::lean_box(0),
                                                            v___x_2481_,
                                                            v___f_2480_,
                                                        );
                                                        return v___x_2482_;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_2467_);
                                                    leanh::lean_dec(v_toTopVar_2429_);
                                                    v___x_2483_ = l_Lean_Meta_Sym_getNatValue_x3f(
                                                        v_arg_2445_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_2483_) == 1
                                                    {
                                                        v_val_2484_ = leanh::lean_ctor_get(
                                                            v___x_2483_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_val_2484_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_2483_,
                                                            1,
                                                        );
                                                        v___f_2485_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17 as *mut core::ffi::c_void, 3, 2);
                                                        leanh::lean_closure_set(
                                                            v___f_2485_,
                                                            0,
                                                            v_val_2484_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2485_,
                                                            1,
                                                            v_toPure_2431_,
                                                        );
                                                        leanh::lean_inc(v_toBind_2439_);
                                                        leanh::lean_inc_ref(v_inst_2436_);
                                                        leanh::lean_inc_ref(v_inst_2435_);
                                                        leanh::lean_inc_ref(v_inst_2434_);
                                                        leanh::lean_inc_ref(v_inst_2433_);
                                                        leanh::lean_inc(v_inst_2432_);
                                                        v___f_2486_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            0,
                                                            v_arg_2453_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            1,
                                                            v_asTopVar_2440_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            2,
                                                            v_e_2430_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            3,
                                                            v_inst_2432_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            4,
                                                            v_inst_2433_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            5,
                                                            v_inst_2434_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            6,
                                                            v_inst_2435_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            7,
                                                            v_inst_2436_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            8,
                                                            v_toVar_2437_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            9,
                                                            v_asVar_2438_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            10,
                                                            v_arg_2449_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            11,
                                                            v_toBind_2439_,
                                                        );
                                                        leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            12,
                                                            v___f_2485_,
                                                        );
                                                        v___x_2487_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_);
                                                        v___x_2488_ = leanh::lean_apply_4(
                                                            v_toBind_2439_,
                                                            leanh::lean_box(0),
                                                            leanh::lean_box(0),
                                                            v___x_2487_,
                                                            v___f_2486_,
                                                        );
                                                        return v___x_2488_;
                                                    } else {
                                                        leanh::lean_dec(v___x_2483_);
                                                        leanh::lean_dec_ref(v_arg_2453_);
                                                        leanh::lean_dec_ref(v_arg_2449_);
                                                        leanh::lean_dec(v_asTopVar_2440_);
                                                        leanh::lean_dec(v_toBind_2439_);
                                                        leanh::lean_dec(v_asVar_2438_);
                                                        leanh::lean_dec(v_toVar_2437_);
                                                        leanh::lean_dec_ref(v_inst_2436_);
                                                        leanh::lean_dec_ref(v_inst_2435_);
                                                        leanh::lean_dec_ref(v_inst_2434_);
                                                        leanh::lean_dec_ref(v_inst_2433_);
                                                        leanh::lean_dec(v_inst_2432_);
                                                        leanh::lean_dec_ref(v_e_2430_);
                                                        v___x_2489_ = leanh::lean_box(0);
                                                        v___x_2490_ = leanh::lean_apply_2(
                                                            v_toPure_2431_,
                                                            leanh::lean_box(0),
                                                            v___x_2489_,
                                                        );
                                                        return v___x_2490_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2454_);
                                    leanh::lean_dec_ref(v_arg_2453_);
                                    leanh::lean_dec(v_asVar_2438_);
                                    leanh::lean_dec(v_toVar_2437_);
                                    leanh::lean_dec_ref(v_inst_2433_);
                                    v___f_2491_ = leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed as *mut core::ffi::c_void, 7, 6);
                                    leanh::lean_closure_set(v___f_2491_, 0, v_arg_2449_);
                                    leanh::lean_closure_set(
                                        v___f_2491_,
                                        1,
                                        v_asTopVar_2440_,
                                    );
                                    leanh::lean_closure_set(v___f_2491_, 2, v_e_2430_);
                                    leanh::lean_closure_set(v___f_2491_, 3, v_arg_2445_);
                                    leanh::lean_closure_set(v___f_2491_, 4, v_toPure_2431_);
                                    leanh::lean_closure_set(
                                        v___f_2491_,
                                        5,
                                        v_toTopVar_2429_,
                                    );
                                    v___x_2492_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
                                        v_inst_2432_,
                                        v_inst_2434_,
                                        v_inst_2435_,
                                        v_inst_2436_,
                                    );
                                    v___x_2493_ = leanh::lean_apply_4(
                                        v_toBind_2439_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2492_,
                                        v___f_2491_,
                                    );
                                    return v___x_2493_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_2454_);
                                leanh::lean_dec_ref(v_arg_2453_);
                                leanh::lean_dec_ref(v_arg_2445_);
                                leanh::lean_dec(v_toBind_2439_);
                                leanh::lean_dec(v_asVar_2438_);
                                leanh::lean_dec(v_toVar_2437_);
                                leanh::lean_dec_ref(v_inst_2436_);
                                leanh::lean_dec_ref(v_inst_2435_);
                                leanh::lean_dec_ref(v_inst_2434_);
                                leanh::lean_dec_ref(v_inst_2433_);
                                leanh::lean_dec(v_inst_2432_);
                                leanh::lean_dec(v_toTopVar_2429_);
                                if leanh::lean_obj_tag(v_arg_2449_) == 9 {
                                    v_a_2494_ = leanh::lean_ctor_get(v_arg_2449_, 0);
                                    leanh::lean_inc_ref(v_a_2494_);
                                    leanh::lean_dec_ref_known(v_arg_2449_, 1);
                                    if leanh::lean_obj_tag(v_a_2494_) == 0 {
                                        leanh::lean_dec(v_asTopVar_2440_);
                                        leanh::lean_dec_ref(v_e_2430_);
                                        v_val_2495_ = leanh::lean_ctor_get(v_a_2494_, 0);
                                        v_isSharedCheck_2505_ =
                                            (!leanh::lean_is_exclusive(v_a_2494_)) as u8;
                                        if v_isSharedCheck_2505_ == 0 {
                                            v___x_2497_ = v_a_2494_;
                                            v_isShared_2498_ = v_isSharedCheck_2505_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_val_2495_);
                                            leanh::lean_dec(v_a_2494_);
                                            v___x_2497_ = leanh::lean_box(0);
                                            v_isShared_2498_ = v_isSharedCheck_2505_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_a_2494_);
                                        leanh::lean_dec(v_toPure_2431_);
                                        v___x_2506_ =
                                            leanh::lean_apply_1(v_asTopVar_2440_, v_e_2430_);
                                        return v___x_2506_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_2449_);
                                    leanh::lean_dec(v_toPure_2431_);
                                    v___x_2507_ =
                                        leanh::lean_apply_1(v_asTopVar_2440_, v_e_2430_);
                                    return v___x_2507_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2499_ = lean_nat_to_int(v_val_2495_);
                if v_isShared_2498_ == 0 {
                    leanh::lean_ctor_set(v___x_2497_, 0, v___x_2499_);
                    v___x_2501_ = v___x_2497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2504_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2499_);
                    v___x_2501_ = v_reuseFailAlloc_2504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2502_, 0, v___x_2501_);
                v___x_2503_ = leanh::lean_apply_2(
                    v_toPure_2431_,
                    leanh::lean_box(0),
                    v___x_2502_,
                );
                return v___x_2503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(
    mut v_inst_2508_: *mut leanh::LeanObject,
    mut v_inst_2509_: *mut leanh::LeanObject,
    mut v_inst_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_inst_2513_: *mut leanh::LeanObject,
    mut v_inst_2514_: *mut leanh::LeanObject,
    mut v_e_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asVar_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toVar_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTopVar_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asTopVar_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2516_ = leanh::lean_ctor_get(v_inst_2511_, 0);
    v_toBind_2517_ = leanh::lean_ctor_get(v_inst_2511_, 1);
    leanh::lean_inc_n(v_toBind_2517_, 6);
    v_toPure_2518_ = leanh::lean_ctor_get(v_toApplicative_2516_, 1);
    leanh::lean_inc_n(v_toPure_2518_, 3);
    v___f_2519_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2519_, 0, v_toPure_2518_);
    v___f_2520_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2520_, 0, v_toPure_2518_);
    leanh::lean_inc(v_inst_2508_);
    leanh::lean_inc_ref(v___f_2520_);
    leanh::lean_inc(v_inst_2514_);
    v_asVar_2521_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v_asVar_2521_, 0, v_inst_2514_);
    leanh::lean_closure_set(v_asVar_2521_, 1, v_toBind_2517_);
    leanh::lean_closure_set(v_asVar_2521_, 2, v___f_2520_);
    leanh::lean_closure_set(v_asVar_2521_, 3, v_inst_2508_);
    v_toVar_2522_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v_toVar_2522_, 0, v_inst_2514_);
    leanh::lean_closure_set(v_toVar_2522_, 1, v_toBind_2517_);
    leanh::lean_closure_set(v_toVar_2522_, 2, v___f_2520_);
    leanh::lean_inc_ref(v_toVar_2522_);
    v_toTopVar_2523_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v_toTopVar_2523_, 0, v_toVar_2522_);
    leanh::lean_closure_set(v_toTopVar_2523_, 1, v_toBind_2517_);
    leanh::lean_closure_set(v_toTopVar_2523_, 2, v___f_2519_);
    leanh::lean_inc_ref(v_toTopVar_2523_);
    v_asTopVar_2524_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v_asTopVar_2524_, 0, v_toTopVar_2523_);
    leanh::lean_closure_set(v_asTopVar_2524_, 1, v_inst_2508_);
    leanh::lean_closure_set(v_asTopVar_2524_, 2, v_toBind_2517_);
    leanh::lean_inc(v_inst_2509_);
    leanh::lean_inc_ref(v_e_2515_);
    v___f_2525_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5 as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_2525_, 0, v_toTopVar_2523_);
    leanh::lean_closure_set(v___f_2525_, 1, v_e_2515_);
    leanh::lean_closure_set(v___f_2525_, 2, v_toPure_2518_);
    leanh::lean_closure_set(v___f_2525_, 3, v_inst_2509_);
    leanh::lean_closure_set(v___f_2525_, 4, v_inst_2510_);
    leanh::lean_closure_set(v___f_2525_, 5, v_inst_2511_);
    leanh::lean_closure_set(v___f_2525_, 6, v_inst_2512_);
    leanh::lean_closure_set(v___f_2525_, 7, v_inst_2513_);
    leanh::lean_closure_set(v___f_2525_, 8, v_toVar_2522_);
    leanh::lean_closure_set(v___f_2525_, 9, v_asVar_2521_);
    leanh::lean_closure_set(v___f_2525_, 10, v_toBind_2517_);
    leanh::lean_closure_set(v___f_2525_, 11, v_asTopVar_2524_);
    v___x_2526_ = leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_2526_, 0, v_e_2515_);
    v___x_2527_ = leanh::lean_apply_2(v_inst_2509_, leanh::lean_box(0), v___x_2526_);
    v___x_2528_ = leanh::lean_apply_4(
        v_toBind_2517_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2527_,
        v___f_2525_,
    );
    return v___x_2528_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f(
    mut v_m_2529_: *mut leanh::LeanObject,
    mut v_inst_2530_: *mut leanh::LeanObject,
    mut v_inst_2531_: *mut leanh::LeanObject,
    mut v_inst_2532_: *mut leanh::LeanObject,
    mut v_inst_2533_: *mut leanh::LeanObject,
    mut v_inst_2534_: *mut leanh::LeanObject,
    mut v_inst_2535_: *mut leanh::LeanObject,
    mut v_inst_2536_: *mut leanh::LeanObject,
    mut v_e_2537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(
        v_inst_2530_,
        v_inst_2531_,
        v_inst_2532_,
        v_inst_2533_,
        v_inst_2534_,
        v_inst_2535_,
        v_inst_2536_,
        v_e_2537_,
    );
    return v___x_2538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Reify(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Reify(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Reify(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Reify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Reify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Reify(builtin);
}