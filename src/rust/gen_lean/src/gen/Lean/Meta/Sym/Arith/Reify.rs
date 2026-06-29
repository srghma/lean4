// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Reify
// Imports: Lean.Meta.Sym.Arith.Functions Lean.Meta.Sym.Arith.MonadVar Lean.Meta.Sym.LitValues
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
use crate::ffi::lean_nat_to_int;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [114, 105, 110, 103, 32, 116, 101, 114, 109, 32, 119, 105, 116, 104, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value) as *mut crate::leanh::LeanObject,7578295756008745317 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value) as *mut crate::leanh::LeanObject,5779414593499529281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value) as *mut crate::leanh::LeanObject,7063772860359172143 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value) as *mut crate::leanh::LeanObject,4977321555018234431 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value) as *mut crate::leanh::LeanObject,4463466624472370110 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value) as *mut crate::leanh::LeanObject,10422657989269798688 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [115, 101, 109, 105, 114, 105, 110, 103, 32, 116, 101, 114, 109, 32, 119, 105, 116, 104, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(
    mut v_inst_1270_: *mut crate::leanh::LeanObject,
    mut v_toPure_1271_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: u8 = 0;
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lean_Expr_appArg_x21(v_____do__lift_1272_);
    v___x_1274_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1273_,
        v_inst_1270_,
    );
    crate::leanh::lean_dec_ref(v___x_1273_);
    v___x_1275_ = crate::leanh::lean_box((v___x_1274_) as usize);
    v___x_1276_ =
        crate::leanh::lean_apply_2(v_toPure_1271_, crate::leanh::lean_box(0), v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed(
    mut v_inst_1277_: *mut crate::leanh::LeanObject,
    mut v_toPure_1278_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(
        v_inst_1277_,
        v_toPure_1278_,
        v_____do__lift_1279_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1279_);
    crate::leanh::lean_dec_ref(v_inst_1277_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst___redArg(
    mut v_inst_1281_: *mut crate::leanh::LeanObject,
    mut v_inst_1282_: *mut crate::leanh::LeanObject,
    mut v_inst_1283_: *mut crate::leanh::LeanObject,
    mut v_inst_1284_: *mut crate::leanh::LeanObject,
    mut v_inst_1285_: *mut crate::leanh::LeanObject,
    mut v_inst_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1287_ = crate::leanh::lean_ctor_get(v_inst_1283_, 0);
    v_toBind_1288_ = crate::leanh::lean_ctor_get(v_inst_1283_, 1);
    crate::leanh::lean_inc(v_toBind_1288_);
    v_toPure_1289_ = crate::leanh::lean_ctor_get(v_toApplicative_1287_, 1);
    crate::leanh::lean_inc(v_toPure_1289_);
    v___x_1290_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(
        v_inst_1281_,
        v_inst_1282_,
        v_inst_1283_,
        v_inst_1284_,
        v_inst_1285_,
    );
    v___f_1291_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1291_, 0, v_inst_1286_);
    crate::leanh::lean_closure_set(v___f_1291_, 1, v_toPure_1289_);
    v___x_1292_ = crate::leanh::lean_apply_4(
        v_toBind_1288_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1290_,
        v___f_1291_,
    );
    return v___x_1292_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isAddInst(
    mut v_m_1293_: *mut crate::leanh::LeanObject,
    mut v_inst_1294_: *mut crate::leanh::LeanObject,
    mut v_inst_1295_: *mut crate::leanh::LeanObject,
    mut v_inst_1296_: *mut crate::leanh::LeanObject,
    mut v_inst_1297_: *mut crate::leanh::LeanObject,
    mut v_inst_1298_: *mut crate::leanh::LeanObject,
    mut v_inst_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1301_: *mut crate::leanh::LeanObject,
    mut v_inst_1302_: *mut crate::leanh::LeanObject,
    mut v_inst_1303_: *mut crate::leanh::LeanObject,
    mut v_inst_1304_: *mut crate::leanh::LeanObject,
    mut v_inst_1305_: *mut crate::leanh::LeanObject,
    mut v_inst_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1307_ = crate::leanh::lean_ctor_get(v_inst_1303_, 0);
    v_toBind_1308_ = crate::leanh::lean_ctor_get(v_inst_1303_, 1);
    crate::leanh::lean_inc(v_toBind_1308_);
    v_toPure_1309_ = crate::leanh::lean_ctor_get(v_toApplicative_1307_, 1);
    crate::leanh::lean_inc(v_toPure_1309_);
    v___x_1310_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(
        v_inst_1301_,
        v_inst_1302_,
        v_inst_1303_,
        v_inst_1304_,
        v_inst_1305_,
    );
    v___f_1311_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1311_, 0, v_inst_1306_);
    crate::leanh::lean_closure_set(v___f_1311_, 1, v_toPure_1309_);
    v___x_1312_ = crate::leanh::lean_apply_4(
        v_toBind_1308_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1310_,
        v___f_1311_,
    );
    return v___x_1312_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isMulInst(
    mut v_m_1313_: *mut crate::leanh::LeanObject,
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
    mut v_inst_1315_: *mut crate::leanh::LeanObject,
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
    mut v_inst_1317_: *mut crate::leanh::LeanObject,
    mut v_inst_1318_: *mut crate::leanh::LeanObject,
    mut v_inst_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1321_: *mut crate::leanh::LeanObject,
    mut v_inst_1322_: *mut crate::leanh::LeanObject,
    mut v_inst_1323_: *mut crate::leanh::LeanObject,
    mut v_inst_1324_: *mut crate::leanh::LeanObject,
    mut v_inst_1325_: *mut crate::leanh::LeanObject,
    mut v_inst_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1327_ = crate::leanh::lean_ctor_get(v_inst_1323_, 0);
    v_toBind_1328_ = crate::leanh::lean_ctor_get(v_inst_1323_, 1);
    crate::leanh::lean_inc(v_toBind_1328_);
    v_toPure_1329_ = crate::leanh::lean_ctor_get(v_toApplicative_1327_, 1);
    crate::leanh::lean_inc(v_toPure_1329_);
    v___x_1330_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(
        v_inst_1321_,
        v_inst_1322_,
        v_inst_1323_,
        v_inst_1324_,
        v_inst_1325_,
    );
    v___f_1331_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1331_, 0, v_inst_1326_);
    crate::leanh::lean_closure_set(v___f_1331_, 1, v_toPure_1329_);
    v___x_1332_ = crate::leanh::lean_apply_4(
        v_toBind_1328_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1330_,
        v___f_1331_,
    );
    return v___x_1332_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isSubInst(
    mut v_m_1333_: *mut crate::leanh::LeanObject,
    mut v_inst_1334_: *mut crate::leanh::LeanObject,
    mut v_inst_1335_: *mut crate::leanh::LeanObject,
    mut v_inst_1336_: *mut crate::leanh::LeanObject,
    mut v_inst_1337_: *mut crate::leanh::LeanObject,
    mut v_inst_1338_: *mut crate::leanh::LeanObject,
    mut v_inst_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1341_: *mut crate::leanh::LeanObject,
    mut v_inst_1342_: *mut crate::leanh::LeanObject,
    mut v_inst_1343_: *mut crate::leanh::LeanObject,
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_inst_1345_: *mut crate::leanh::LeanObject,
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1347_ = crate::leanh::lean_ctor_get(v_inst_1343_, 0);
    v_toBind_1348_ = crate::leanh::lean_ctor_get(v_inst_1343_, 1);
    crate::leanh::lean_inc(v_toBind_1348_);
    v_toPure_1349_ = crate::leanh::lean_ctor_get(v_toApplicative_1347_, 1);
    crate::leanh::lean_inc(v_toPure_1349_);
    v___x_1350_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(
        v_inst_1341_,
        v_inst_1342_,
        v_inst_1343_,
        v_inst_1344_,
        v_inst_1345_,
    );
    v___f_1351_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1351_, 0, v_inst_1346_);
    crate::leanh::lean_closure_set(v___f_1351_, 1, v_toPure_1349_);
    v___x_1352_ = crate::leanh::lean_apply_4(
        v_toBind_1348_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1350_,
        v___f_1351_,
    );
    return v___x_1352_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isNegInst(
    mut v_m_1353_: *mut crate::leanh::LeanObject,
    mut v_inst_1354_: *mut crate::leanh::LeanObject,
    mut v_inst_1355_: *mut crate::leanh::LeanObject,
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_inst_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_inst_1362_: *mut crate::leanh::LeanObject,
    mut v_inst_1363_: *mut crate::leanh::LeanObject,
    mut v_inst_1364_: *mut crate::leanh::LeanObject,
    mut v_inst_1365_: *mut crate::leanh::LeanObject,
    mut v_inst_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1367_ = crate::leanh::lean_ctor_get(v_inst_1363_, 0);
    v_toBind_1368_ = crate::leanh::lean_ctor_get(v_inst_1363_, 1);
    crate::leanh::lean_inc(v_toBind_1368_);
    v_toPure_1369_ = crate::leanh::lean_ctor_get(v_toApplicative_1367_, 1);
    crate::leanh::lean_inc(v_toPure_1369_);
    v___x_1370_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(
        v_inst_1361_,
        v_inst_1362_,
        v_inst_1363_,
        v_inst_1364_,
        v_inst_1365_,
    );
    v___f_1371_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1371_, 0, v_inst_1366_);
    crate::leanh::lean_closure_set(v___f_1371_, 1, v_toPure_1369_);
    v___x_1372_ = crate::leanh::lean_apply_4(
        v_toBind_1368_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1370_,
        v___f_1371_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isPowInst(
    mut v_m_1373_: *mut crate::leanh::LeanObject,
    mut v_inst_1374_: *mut crate::leanh::LeanObject,
    mut v_inst_1375_: *mut crate::leanh::LeanObject,
    mut v_inst_1376_: *mut crate::leanh::LeanObject,
    mut v_inst_1377_: *mut crate::leanh::LeanObject,
    mut v_inst_1378_: *mut crate::leanh::LeanObject,
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1381_: *mut crate::leanh::LeanObject,
    mut v_inst_1382_: *mut crate::leanh::LeanObject,
    mut v_inst_1383_: *mut crate::leanh::LeanObject,
    mut v_inst_1384_: *mut crate::leanh::LeanObject,
    mut v_inst_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1386_ = crate::leanh::lean_ctor_get(v_inst_1382_, 0);
    v_toBind_1387_ = crate::leanh::lean_ctor_get(v_inst_1382_, 1);
    crate::leanh::lean_inc(v_toBind_1387_);
    v_toPure_1388_ = crate::leanh::lean_ctor_get(v_toApplicative_1386_, 1);
    crate::leanh::lean_inc(v_toPure_1388_);
    v___x_1389_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(
        v_inst_1381_,
        v_inst_1382_,
        v_inst_1383_,
        v_inst_1384_,
    );
    v___f_1390_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1390_, 0, v_inst_1385_);
    crate::leanh::lean_closure_set(v___f_1390_, 1, v_toPure_1388_);
    v___x_1391_ = crate::leanh::lean_apply_4(
        v_toBind_1387_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1389_,
        v___f_1390_,
    );
    return v___x_1391_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isIntCastInst(
    mut v_m_1392_: *mut crate::leanh::LeanObject,
    mut v_inst_1393_: *mut crate::leanh::LeanObject,
    mut v_inst_1394_: *mut crate::leanh::LeanObject,
    mut v_inst_1395_: *mut crate::leanh::LeanObject,
    mut v_inst_1396_: *mut crate::leanh::LeanObject,
    mut v_inst_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1399_: *mut crate::leanh::LeanObject,
    mut v_inst_1400_: *mut crate::leanh::LeanObject,
    mut v_inst_1401_: *mut crate::leanh::LeanObject,
    mut v_inst_1402_: *mut crate::leanh::LeanObject,
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1404_ = crate::leanh::lean_ctor_get(v_inst_1400_, 0);
    v_toBind_1405_ = crate::leanh::lean_ctor_get(v_inst_1400_, 1);
    crate::leanh::lean_inc(v_toBind_1405_);
    v_toPure_1406_ = crate::leanh::lean_ctor_get(v_toApplicative_1404_, 1);
    crate::leanh::lean_inc(v_toPure_1406_);
    v___x_1407_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
        v_inst_1399_,
        v_inst_1400_,
        v_inst_1401_,
        v_inst_1402_,
    );
    v___f_1408_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1408_, 0, v_inst_1403_);
    crate::leanh::lean_closure_set(v___f_1408_, 1, v_toPure_1406_);
    v___x_1409_ = crate::leanh::lean_apply_4(
        v_toBind_1405_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1407_,
        v___f_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_isNatCastInst(
    mut v_m_1410_: *mut crate::leanh::LeanObject,
    mut v_inst_1411_: *mut crate::leanh::LeanObject,
    mut v_inst_1412_: *mut crate::leanh::LeanObject,
    mut v_inst_1413_: *mut crate::leanh::LeanObject,
    mut v_inst_1414_: *mut crate::leanh::LeanObject,
    mut v_inst_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1418_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0;
    v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
    mut v_inst_1420_: *mut crate::leanh::LeanObject,
    mut v_e_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1);
    v___x_1423_ = l_Lean_indentExpr(v_e_1421_);
    v___x_1424_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1424_, 0, v___x_1422_);
    crate::leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
    v___x_1425_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_reportIssueIfVerbose___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1425_, 0, v___x_1424_);
    v___x_1426_ = crate::leanh::lean_apply_2(v_inst_1420_, crate::leanh::lean_box(0), v___x_1425_);
    return v___x_1426_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue(
    mut v_m_1427_: *mut crate::leanh::LeanObject,
    mut v_inst_1428_: *mut crate::leanh::LeanObject,
    mut v_e_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
            v_inst_1428_,
            v_e_1429_,
        );
    return v___x_1430_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0(
    mut v_toPure_1431_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1433_, 0, v_____do__lift_1432_);
    v___x_1434_ =
        crate::leanh::lean_apply_2(v_toPure_1431_, crate::leanh::lean_box(0), v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1(
    mut v_____do__lift_1435_: *mut crate::leanh::LeanObject,
    mut v_toPure_1436_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1438_, 0, v_____do__lift_1435_);
    crate::leanh::lean_ctor_set(v___x_1438_, 1, v_____do__lift_1437_);
    v___x_1439_ =
        crate::leanh::lean_apply_2(v_toPure_1436_, crate::leanh::lean_box(0), v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(
    mut v_asVar_1440_: *mut crate::leanh::LeanObject,
    mut v_e_1441_: *mut crate::leanh::LeanObject,
    mut v_arg_1442_: *mut crate::leanh::LeanObject,
    mut v_toPure_1443_: *mut crate::leanh::LeanObject,
    mut v_toVar_1444_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1445_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1445_ == 0 {
                    crate::leanh::lean_dec(v_toVar_1444_);
                    crate::leanh::lean_dec(v_toPure_1443_);
                    crate::leanh::lean_dec_ref(v_arg_1442_);
                    v___x_1446_ = crate::leanh::lean_apply_1(v_asVar_1440_, v_e_1441_);
                    return v___x_1446_;
                } else {
                    crate::leanh::lean_dec(v_asVar_1440_);
                    v___x_1447_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_1442_);
                    if crate::leanh::lean_obj_tag(v___x_1447_) == 1 {
                        crate::leanh::lean_dec(v_toVar_1444_);
                        crate::leanh::lean_dec_ref(v_e_1441_);
                        v_val_1448_ = crate::leanh::lean_ctor_get(v___x_1447_, 0);
                        v_isSharedCheck_1456_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1447_)) as u8;
                        if v_isSharedCheck_1456_ == 0 {
                            v___x_1450_ = v___x_1447_;
                            v_isShared_1451_ = v_isSharedCheck_1456_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1448_);
                            crate::leanh::lean_dec(v___x_1447_);
                            v___x_1450_ = crate::leanh::lean_box(0);
                            v_isShared_1451_ = v_isSharedCheck_1456_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1447_);
                        crate::leanh::lean_dec(v_toPure_1443_);
                        v___x_1457_ = crate::leanh::lean_apply_1(v_toVar_1444_, v_e_1441_);
                        return v___x_1457_;
                    }
                }
            }
            1 => {
                if v_isShared_1451_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1450_, 2);
                    v___x_1453_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1448_);
                    v___x_1453_ = v_reuseFailAlloc_1455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1454_ = crate::leanh::lean_apply_2(
                    v_toPure_1443_,
                    crate::leanh::lean_box(0),
                    v___x_1453_,
                );
                return v___x_1454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed(
    mut v_asVar_1458_: *mut crate::leanh::LeanObject,
    mut v_e_1459_: *mut crate::leanh::LeanObject,
    mut v_arg_1460_: *mut crate::leanh::LeanObject,
    mut v_toPure_1461_: *mut crate::leanh::LeanObject,
    mut v_toVar_1462_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_4904__boxed_1464_: u8 = 0;
    let mut v_res_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4904__boxed_1464_ = (crate::leanh::lean_unbox(v_____do__lift_1463_) as u8);
    v_res_1465_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_1458_, v_e_1459_, v_arg_1460_, v_toPure_1461_, v_toVar_1462_, v_____do__lift_4904__boxed_1464_);
    return v_res_1465_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7(
    mut v_____do__lift_1466_: *mut crate::leanh::LeanObject,
    mut v_toPure_1467_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1469_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1469_, 0, v_____do__lift_1466_);
    crate::leanh::lean_ctor_set(v___x_1469_, 1, v_____do__lift_1468_);
    v___x_1470_ =
        crate::leanh::lean_apply_2(v_toPure_1467_, crate::leanh::lean_box(0), v___x_1469_);
    return v___x_1470_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4(
    mut v_____do__lift_1471_: *mut crate::leanh::LeanObject,
    mut v_toPure_1472_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1474_, 0, v_____do__lift_1471_);
    crate::leanh::lean_ctor_set(v___x_1474_, 1, v_____do__lift_1473_);
    v___x_1475_ =
        crate::leanh::lean_apply_2(v_toPure_1472_, crate::leanh::lean_box(0), v___x_1474_);
    return v___x_1475_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9(
    mut v_val_1476_: *mut crate::leanh::LeanObject,
    mut v_toPure_1477_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1479_, 0, v_____do__lift_1478_);
    crate::leanh::lean_ctor_set(v___x_1479_, 1, v_val_1476_);
    v___x_1480_ =
        crate::leanh::lean_apply_2(v_toPure_1477_, crate::leanh::lean_box(0), v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(
    mut v_asVar_1481_: *mut crate::leanh::LeanObject,
    mut v_e_1482_: *mut crate::leanh::LeanObject,
    mut v_arg_1483_: *mut crate::leanh::LeanObject,
    mut v_toPure_1484_: *mut crate::leanh::LeanObject,
    mut v_toVar_1485_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1486_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1486_ == 0 {
                    crate::leanh::lean_dec(v_toVar_1485_);
                    crate::leanh::lean_dec(v_toPure_1484_);
                    crate::leanh::lean_dec_ref(v_arg_1483_);
                    v___x_1487_ = crate::leanh::lean_apply_1(v_asVar_1481_, v_e_1482_);
                    return v___x_1487_;
                } else {
                    crate::leanh::lean_dec(v_asVar_1481_);
                    v___x_1488_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1483_);
                    if crate::leanh::lean_obj_tag(v___x_1488_) == 1 {
                        crate::leanh::lean_dec(v_toVar_1485_);
                        crate::leanh::lean_dec_ref(v_e_1482_);
                        v_val_1489_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
                        v_isSharedCheck_1497_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1488_)) as u8;
                        if v_isSharedCheck_1497_ == 0 {
                            v___x_1491_ = v___x_1488_;
                            v_isShared_1492_ = v_isSharedCheck_1497_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1489_);
                            crate::leanh::lean_dec(v___x_1488_);
                            v___x_1491_ = crate::leanh::lean_box(0);
                            v_isShared_1492_ = v_isSharedCheck_1497_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1488_);
                        crate::leanh::lean_dec(v_toPure_1484_);
                        v___x_1498_ = crate::leanh::lean_apply_1(v_toVar_1485_, v_e_1482_);
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
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_val_1489_);
                    v___x_1494_ = v_reuseFailAlloc_1496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1495_ = crate::leanh::lean_apply_2(
                    v_toPure_1484_,
                    crate::leanh::lean_box(0),
                    v___x_1494_,
                );
                return v___x_1495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed(
    mut v_asVar_1499_: *mut crate::leanh::LeanObject,
    mut v_e_1500_: *mut crate::leanh::LeanObject,
    mut v_arg_1501_: *mut crate::leanh::LeanObject,
    mut v_toPure_1502_: *mut crate::leanh::LeanObject,
    mut v_toVar_1503_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_4958__boxed_1505_: u8 = 0;
    let mut v_res_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4958__boxed_1505_ = (crate::leanh::lean_unbox(v_____do__lift_1504_) as u8);
    v_res_1506_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_1499_, v_e_1500_, v_arg_1501_, v_toPure_1502_, v_toVar_1503_, v_____do__lift_4958__boxed_1505_);
    return v_res_1506_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(
    mut v_asVar_1551_: *mut crate::leanh::LeanObject,
    mut v_e_1552_: *mut crate::leanh::LeanObject,
    mut v_inst_1553_: *mut crate::leanh::LeanObject,
    mut v_inst_1554_: *mut crate::leanh::LeanObject,
    mut v_inst_1555_: *mut crate::leanh::LeanObject,
    mut v_inst_1556_: *mut crate::leanh::LeanObject,
    mut v_inst_1557_: *mut crate::leanh::LeanObject,
    mut v_toVar_1558_: *mut crate::leanh::LeanObject,
    mut v_arg_1559_: *mut crate::leanh::LeanObject,
    mut v_toBind_1560_: *mut crate::leanh::LeanObject,
    mut v___f_1561_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1562_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1562_ == 0 {
        let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1561_);
        crate::leanh::lean_dec(v_toBind_1560_);
        crate::leanh::lean_dec_ref(v_arg_1559_);
        crate::leanh::lean_dec(v_toVar_1558_);
        crate::leanh::lean_dec_ref(v_inst_1557_);
        crate::leanh::lean_dec_ref(v_inst_1556_);
        crate::leanh::lean_dec_ref(v_inst_1555_);
        crate::leanh::lean_dec_ref(v_inst_1554_);
        crate::leanh::lean_dec(v_inst_1553_);
        v___x_1563_ = crate::leanh::lean_apply_1(v_asVar_1551_, v_e_1552_);
        return v___x_1563_;
    } else {
        let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_1552_);
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
        v___x_1565_ = crate::leanh::lean_apply_4(
            v_toBind_1560_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1564_,
            v___f_1561_,
        );
        return v___x_1565_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed(
    mut v_asVar_1566_: *mut crate::leanh::LeanObject,
    mut v_e_1567_: *mut crate::leanh::LeanObject,
    mut v_inst_1568_: *mut crate::leanh::LeanObject,
    mut v_inst_1569_: *mut crate::leanh::LeanObject,
    mut v_inst_1570_: *mut crate::leanh::LeanObject,
    mut v_inst_1571_: *mut crate::leanh::LeanObject,
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_toVar_1573_: *mut crate::leanh::LeanObject,
    mut v_arg_1574_: *mut crate::leanh::LeanObject,
    mut v_toBind_1575_: *mut crate::leanh::LeanObject,
    mut v___f_1576_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_5068__boxed_1578_: u8 = 0;
    let mut v_res_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_5068__boxed_1578_ = (crate::leanh::lean_unbox(v_____do__lift_1577_) as u8);
    v_res_1579_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_1566_, v_e_1567_, v_inst_1568_, v_inst_1569_, v_inst_1570_, v_inst_1571_, v_inst_1572_, v_toVar_1573_, v_arg_1574_, v_toBind_1575_, v___f_1576_, v_____do__lift_5068__boxed_1578_);
    return v_res_1579_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5(
    mut v_toPure_1580_: *mut crate::leanh::LeanObject,
    mut v_inst_1581_: *mut crate::leanh::LeanObject,
    mut v_inst_1582_: *mut crate::leanh::LeanObject,
    mut v_inst_1583_: *mut crate::leanh::LeanObject,
    mut v_inst_1584_: *mut crate::leanh::LeanObject,
    mut v_inst_1585_: *mut crate::leanh::LeanObject,
    mut v_toVar_1586_: *mut crate::leanh::LeanObject,
    mut v_asVar_1587_: *mut crate::leanh::LeanObject,
    mut v_arg_1588_: *mut crate::leanh::LeanObject,
    mut v_toBind_1589_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1591_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1591_, 0, v_____do__lift_1590_);
    crate::leanh::lean_closure_set(v___f_1591_, 1, v_toPure_1580_);
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
    v___x_1593_ = crate::leanh::lean_apply_4(
        v_toBind_1589_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1592_,
        v___f_1591_,
    );
    return v___x_1593_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6(
    mut v_toPure_1594_: *mut crate::leanh::LeanObject,
    mut v_inst_1595_: *mut crate::leanh::LeanObject,
    mut v_inst_1596_: *mut crate::leanh::LeanObject,
    mut v_inst_1597_: *mut crate::leanh::LeanObject,
    mut v_inst_1598_: *mut crate::leanh::LeanObject,
    mut v_inst_1599_: *mut crate::leanh::LeanObject,
    mut v_toVar_1600_: *mut crate::leanh::LeanObject,
    mut v_asVar_1601_: *mut crate::leanh::LeanObject,
    mut v_arg_1602_: *mut crate::leanh::LeanObject,
    mut v_toBind_1603_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1605_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1605_, 0, v_____do__lift_1604_);
    crate::leanh::lean_closure_set(v___f_1605_, 1, v_toPure_1594_);
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
    v___x_1607_ = crate::leanh::lean_apply_4(
        v_toBind_1603_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1606_,
        v___f_1605_,
    );
    return v___x_1607_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(
    mut v_toVar_1608_: *mut crate::leanh::LeanObject,
    mut v_e_1609_: *mut crate::leanh::LeanObject,
    mut v_toPure_1610_: *mut crate::leanh::LeanObject,
    mut v_inst_1611_: *mut crate::leanh::LeanObject,
    mut v_inst_1612_: *mut crate::leanh::LeanObject,
    mut v_inst_1613_: *mut crate::leanh::LeanObject,
    mut v_inst_1614_: *mut crate::leanh::LeanObject,
    mut v_inst_1615_: *mut crate::leanh::LeanObject,
    mut v_asVar_1616_: *mut crate::leanh::LeanObject,
    mut v_toBind_1617_: *mut crate::leanh::LeanObject,
    mut v___f_1618_: *mut crate::leanh::LeanObject,
    mut v_____x_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1635_ = l_Lean_Expr_cleanupAnnotations(v_____x_1619_);
                v___x_1636_ = l_Lean_Expr_isApp(v___x_1635_);
                if v___x_1636_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1635_);
                    crate::leanh::lean_dec(v___f_1618_);
                    crate::leanh::lean_dec(v_toBind_1617_);
                    crate::leanh::lean_dec(v_asVar_1616_);
                    crate::leanh::lean_dec_ref(v_inst_1615_);
                    crate::leanh::lean_dec_ref(v_inst_1614_);
                    crate::leanh::lean_dec_ref(v_inst_1613_);
                    crate::leanh::lean_dec_ref(v_inst_1612_);
                    crate::leanh::lean_dec(v_inst_1611_);
                    crate::leanh::lean_dec(v_toPure_1610_);
                    v___x_1637_ = crate::leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                    return v___x_1637_;
                } else {
                    v_arg_1638_ = crate::leanh::lean_ctor_get(v___x_1635_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1638_);
                    v___x_1639_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1635_);
                    v___x_1640_ = l_Lean_Expr_isApp(v___x_1639_);
                    if v___x_1640_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1639_);
                        crate::leanh::lean_dec_ref(v_arg_1638_);
                        crate::leanh::lean_dec(v___f_1618_);
                        crate::leanh::lean_dec(v_toBind_1617_);
                        crate::leanh::lean_dec(v_asVar_1616_);
                        crate::leanh::lean_dec_ref(v_inst_1615_);
                        crate::leanh::lean_dec_ref(v_inst_1614_);
                        crate::leanh::lean_dec_ref(v_inst_1613_);
                        crate::leanh::lean_dec_ref(v_inst_1612_);
                        crate::leanh::lean_dec(v_inst_1611_);
                        crate::leanh::lean_dec(v_toPure_1610_);
                        v___x_1641_ = crate::leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                        return v___x_1641_;
                    } else {
                        v_arg_1642_ = crate::leanh::lean_ctor_get(v___x_1639_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1642_);
                        v___x_1643_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1639_);
                        v___x_1644_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2;
                        v___x_1645_ = l_Lean_Expr_isConstOf(v___x_1643_, v___x_1644_);
                        if v___x_1645_ == 0 {
                            v___x_1646_ = l_Lean_Expr_isApp(v___x_1643_);
                            if v___x_1646_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1643_);
                                crate::leanh::lean_dec_ref(v_arg_1642_);
                                crate::leanh::lean_dec_ref(v_arg_1638_);
                                crate::leanh::lean_dec(v___f_1618_);
                                crate::leanh::lean_dec(v_toBind_1617_);
                                crate::leanh::lean_dec(v_asVar_1616_);
                                crate::leanh::lean_dec_ref(v_inst_1615_);
                                crate::leanh::lean_dec_ref(v_inst_1614_);
                                crate::leanh::lean_dec_ref(v_inst_1613_);
                                crate::leanh::lean_dec_ref(v_inst_1612_);
                                crate::leanh::lean_dec(v_inst_1611_);
                                crate::leanh::lean_dec(v_toPure_1610_);
                                v___x_1647_ = crate::leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                                return v___x_1647_;
                            } else {
                                v_arg_1648_ = crate::leanh::lean_ctor_get(v___x_1643_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1648_);
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
                                                crate::leanh::lean_dec(v___f_1618_);
                                                v___x_1658_ = l_Lean_Expr_isApp(v___x_1649_);
                                                if v___x_1658_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_1649_);
                                                    crate::leanh::lean_dec_ref(v_arg_1648_);
                                                    crate::leanh::lean_dec_ref(v_arg_1642_);
                                                    crate::leanh::lean_dec_ref(v_arg_1638_);
                                                    crate::leanh::lean_dec(v_toBind_1617_);
                                                    crate::leanh::lean_dec(v_asVar_1616_);
                                                    crate::leanh::lean_dec_ref(v_inst_1615_);
                                                    crate::leanh::lean_dec_ref(v_inst_1614_);
                                                    crate::leanh::lean_dec_ref(v_inst_1613_);
                                                    crate::leanh::lean_dec_ref(v_inst_1612_);
                                                    crate::leanh::lean_dec(v_inst_1611_);
                                                    crate::leanh::lean_dec(v_toPure_1610_);
                                                    v___x_1659_ = crate::leanh::lean_apply_1(
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
                                                        crate::leanh::lean_dec_ref(v___x_1660_);
                                                        crate::leanh::lean_dec_ref(v_arg_1648_);
                                                        crate::leanh::lean_dec_ref(v_arg_1642_);
                                                        crate::leanh::lean_dec_ref(v_arg_1638_);
                                                        crate::leanh::lean_dec(v_toBind_1617_);
                                                        crate::leanh::lean_dec(v_asVar_1616_);
                                                        crate::leanh::lean_dec_ref(v_inst_1615_);
                                                        crate::leanh::lean_dec_ref(v_inst_1614_);
                                                        crate::leanh::lean_dec_ref(v_inst_1613_);
                                                        crate::leanh::lean_dec_ref(v_inst_1612_);
                                                        crate::leanh::lean_dec(v_inst_1611_);
                                                        crate::leanh::lean_dec(v_toPure_1610_);
                                                        v___x_1662_ = crate::leanh::lean_apply_1(
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
                                                            crate::leanh::lean_dec_ref(v___x_1663_);
                                                            crate::leanh::lean_dec_ref(v_arg_1648_);
                                                            crate::leanh::lean_dec_ref(v_arg_1642_);
                                                            crate::leanh::lean_dec_ref(v_arg_1638_);
                                                            crate::leanh::lean_dec(v_toBind_1617_);
                                                            crate::leanh::lean_dec(v_asVar_1616_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_1615_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_1614_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_1613_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_1612_,
                                                            );
                                                            crate::leanh::lean_dec(v_inst_1611_);
                                                            crate::leanh::lean_dec(v_toPure_1610_);
                                                            v___x_1665_ =
                                                                crate::leanh::lean_apply_1(
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
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_1666_,
                                                                        );
                                                                        if v___x_1674_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_1648_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1642_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1638_);
                                                                            crate::leanh::lean_dec(
                                                                                v_toBind_1617_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v_asVar_1616_,
                                                                            );
                                                                            crate::leanh::lean_dec_ref(v_inst_1615_);
                                                                            crate::leanh::lean_dec_ref(v_inst_1614_);
                                                                            crate::leanh::lean_dec_ref(v_inst_1613_);
                                                                            crate::leanh::lean_dec_ref(v_inst_1612_);
                                                                            crate::leanh::lean_dec(
                                                                                v_inst_1611_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v_toPure_1610_,
                                                                            );
                                                                            v___x_1675_ = crate::leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                                                                            return v___x_1675_;
                                                                        } else {
                                                                            crate::leanh::lean_inc_n(v_toBind_1617_, 2);
                                                                            crate::leanh::lean_inc(
                                                                                v_asVar_1616_,
                                                                            );
                                                                            crate::leanh::lean_inc(
                                                                                v_toVar_1608_,
                                                                            );
                                                                            crate::leanh::lean_inc_ref_n(v_inst_1615_, 2);
                                                                            crate::leanh::lean_inc_ref_n(v_inst_1614_, 2);
                                                                            crate::leanh::lean_inc_ref_n(v_inst_1613_, 2);
                                                                            crate::leanh::lean_inc_ref_n(v_inst_1612_, 2);
                                                                            crate::leanh::lean_inc_n(v_inst_1611_, 2);
                                                                            v___f_1676_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2 as *mut core::ffi::c_void, 11, 10);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 0, v_toPure_1610_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 1, v_inst_1611_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 2, v_inst_1612_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 3, v_inst_1613_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 4, v_inst_1614_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 5, v_inst_1615_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 6, v_toVar_1608_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 7, v_asVar_1616_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 8, v_arg_1638_);
                                                                            crate::leanh::lean_closure_set(v___f_1676_, 9, v_toBind_1617_);
                                                                            v___f_1677_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 0, v_asVar_1616_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 1, v_e_1609_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 2, v_inst_1611_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 3, v_inst_1612_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 4, v_inst_1613_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 5, v_inst_1614_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 6, v_inst_1615_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 7, v_toVar_1608_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 8, v_arg_1642_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 9, v_toBind_1617_);
                                                                            crate::leanh::lean_closure_set(v___f_1677_, 10, v___f_1676_);
                                                                            v___x_1678_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                            v___x_1679_ = crate::leanh::lean_apply_4(v_toBind_1617_, crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_1678_, v___f_1677_);
                                                                            return v___x_1679_;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_1666_,
                                                                        );
                                                                        crate::leanh::lean_inc_n(
                                                                            v_toBind_1617_,
                                                                            2,
                                                                        );
                                                                        crate::leanh::lean_inc(
                                                                            v_asVar_1616_,
                                                                        );
                                                                        crate::leanh::lean_inc(
                                                                            v_toVar_1608_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1615_, 2);
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1614_, 2);
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1613_, 2);
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1612_, 2);
                                                                        crate::leanh::lean_inc_n(
                                                                            v_inst_1611_,
                                                                            2,
                                                                        );
                                                                        v___f_1680_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5 as *mut core::ffi::c_void, 11, 10);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 0, v_toPure_1610_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 1, v_inst_1611_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 2, v_inst_1612_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 3, v_inst_1613_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 4, v_inst_1614_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 5, v_inst_1615_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 6, v_toVar_1608_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 7, v_asVar_1616_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 8, v_arg_1638_);
                                                                        crate::leanh::lean_closure_set(v___f_1680_, 9, v_toBind_1617_);
                                                                        v___f_1681_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 0, v_asVar_1616_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 1, v_e_1609_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 2, v_inst_1611_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 3, v_inst_1612_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 4, v_inst_1613_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 5, v_inst_1614_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 6, v_inst_1615_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 7, v_toVar_1608_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 8, v_arg_1642_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 9, v_toBind_1617_);
                                                                        crate::leanh::lean_closure_set(v___f_1681_, 10, v___f_1680_);
                                                                        v___x_1682_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                        v___x_1683_ = crate::leanh::lean_apply_4(v_toBind_1617_, crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_1682_, v___f_1681_);
                                                                        return v___x_1683_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1666_,
                                                                    );
                                                                    crate::leanh::lean_inc_n(
                                                                        v_toBind_1617_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_asVar_1616_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_toVar_1608_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1615_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1614_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1613_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1612_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_n(
                                                                        v_inst_1611_,
                                                                        2,
                                                                    );
                                                                    v___f_1684_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        0,
                                                                        v_toPure_1610_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        1,
                                                                        v_inst_1611_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        2,
                                                                        v_inst_1612_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        3,
                                                                        v_inst_1613_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        4,
                                                                        v_inst_1614_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        5,
                                                                        v_inst_1615_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        6,
                                                                        v_toVar_1608_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        7,
                                                                        v_asVar_1616_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        8,
                                                                        v_arg_1638_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1684_,
                                                                        9,
                                                                        v_toBind_1617_,
                                                                    );
                                                                    v___f_1685_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        0,
                                                                        v_asVar_1616_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        1,
                                                                        v_e_1609_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        2,
                                                                        v_inst_1611_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        3,
                                                                        v_inst_1612_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        4,
                                                                        v_inst_1613_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        5,
                                                                        v_inst_1614_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        6,
                                                                        v_inst_1615_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        7,
                                                                        v_toVar_1608_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        8,
                                                                        v_arg_1642_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        9,
                                                                        v_toBind_1617_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1685_,
                                                                        10,
                                                                        v___f_1684_,
                                                                    );
                                                                    v___x_1686_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                    v___x_1687_ =
                                                                        crate::leanh::lean_apply_4(
                                                                            v_toBind_1617_,
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            v___x_1686_,
                                                                            v___f_1685_,
                                                                        );
                                                                    return v___x_1687_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_1666_,
                                                                );
                                                                v___x_1688_ =
                                                                    l_Lean_Meta_Sym_getNatValue_x3f(
                                                                        v_arg_1638_,
                                                                    );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_1688_,
                                                                ) == 1
                                                                {
                                                                    v_val_1689_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1688_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_val_1689_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_1688_, 1);
                                                                    v___f_1690_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9 as *mut core::ffi::c_void, 3, 2);
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1690_,
                                                                        0,
                                                                        v_val_1689_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1690_,
                                                                        1,
                                                                        v_toPure_1610_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_toBind_1617_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_inst_1615_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_inst_1614_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_inst_1613_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_inst_1612_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_inst_1611_,
                                                                    );
                                                                    v___f_1691_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        0,
                                                                        v_asVar_1616_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        1,
                                                                        v_e_1609_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        2,
                                                                        v_inst_1611_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        3,
                                                                        v_inst_1612_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        4,
                                                                        v_inst_1613_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        5,
                                                                        v_inst_1614_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        6,
                                                                        v_inst_1615_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        7,
                                                                        v_toVar_1608_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        8,
                                                                        v_arg_1642_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        9,
                                                                        v_toBind_1617_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_1691_,
                                                                        10,
                                                                        v___f_1690_,
                                                                    );
                                                                    v___x_1692_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_arg_1648_);
                                                                    v___x_1693_ =
                                                                        crate::leanh::lean_apply_4(
                                                                            v_toBind_1617_,
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            v___x_1692_,
                                                                            v___f_1691_,
                                                                        );
                                                                    return v___x_1693_;
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1688_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1648_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1642_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_toBind_1617_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_asVar_1616_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_inst_1615_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_inst_1614_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_inst_1613_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_inst_1612_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_inst_1611_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_toPure_1610_,
                                                                    );
                                                                    v___x_1694_ =
                                                                        crate::leanh::lean_apply_1(
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
                                                crate::leanh::lean_dec_ref(v___x_1649_);
                                                crate::leanh::lean_dec_ref(v_arg_1648_);
                                                crate::leanh::lean_dec(v_toPure_1610_);
                                                crate::leanh::lean_inc(v_toBind_1617_);
                                                crate::leanh::lean_inc_ref(v_inst_1615_);
                                                crate::leanh::lean_inc_ref(v_inst_1614_);
                                                crate::leanh::lean_inc_ref(v_inst_1613_);
                                                crate::leanh::lean_inc_ref(v_inst_1612_);
                                                crate::leanh::lean_inc(v_inst_1611_);
                                                v___f_1695_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    0,
                                                    v_asVar_1616_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    1,
                                                    v_e_1609_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    2,
                                                    v_inst_1611_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    3,
                                                    v_inst_1612_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    4,
                                                    v_inst_1613_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    5,
                                                    v_inst_1614_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    6,
                                                    v_inst_1615_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    7,
                                                    v_toVar_1608_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    8,
                                                    v_arg_1638_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_1695_,
                                                    9,
                                                    v_toBind_1617_,
                                                );
                                                crate::leanh::lean_closure_set(
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
                                                v___x_1697_ = crate::leanh::lean_apply_4(
                                                    v_toBind_1617_,
                                                    crate::leanh::lean_box(0),
                                                    crate::leanh::lean_box(0),
                                                    v___x_1696_,
                                                    v___f_1695_,
                                                );
                                                return v___x_1697_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1649_);
                                            crate::leanh::lean_dec_ref(v_arg_1648_);
                                            crate::leanh::lean_dec(v___f_1618_);
                                            crate::leanh::lean_dec_ref(v_inst_1612_);
                                            v___f_1698_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed as *mut core::ffi::c_void, 6, 5);
                                            crate::leanh::lean_closure_set(
                                                v___f_1698_,
                                                0,
                                                v_asVar_1616_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_1698_,
                                                1,
                                                v_e_1609_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_1698_,
                                                2,
                                                v_arg_1638_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_1698_,
                                                3,
                                                v_toPure_1610_,
                                            );
                                            crate::leanh::lean_closure_set(
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
                                            v___x_1700_ = crate::leanh::lean_apply_4(
                                                v_toBind_1617_,
                                                crate::leanh::lean_box(0),
                                                crate::leanh::lean_box(0),
                                                v___x_1699_,
                                                v___f_1698_,
                                            );
                                            return v___x_1700_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1649_);
                                        crate::leanh::lean_dec_ref(v_arg_1648_);
                                        crate::leanh::lean_dec(v___f_1618_);
                                        crate::leanh::lean_dec_ref(v_inst_1612_);
                                        v___f_1701_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed as *mut core::ffi::c_void, 6, 5);
                                        crate::leanh::lean_closure_set(
                                            v___f_1701_,
                                            0,
                                            v_asVar_1616_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1701_, 1, v_e_1609_);
                                        crate::leanh::lean_closure_set(v___f_1701_, 2, v_arg_1638_);
                                        crate::leanh::lean_closure_set(
                                            v___f_1701_,
                                            3,
                                            v_toPure_1610_,
                                        );
                                        crate::leanh::lean_closure_set(
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
                                        v___x_1703_ = crate::leanh::lean_apply_4(
                                            v_toBind_1617_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v___x_1702_,
                                            v___f_1701_,
                                        );
                                        return v___x_1703_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1649_);
                                    crate::leanh::lean_dec_ref(v_arg_1648_);
                                    crate::leanh::lean_dec_ref(v_arg_1638_);
                                    crate::leanh::lean_dec(v___f_1618_);
                                    crate::leanh::lean_dec(v_toBind_1617_);
                                    crate::leanh::lean_dec(v_asVar_1616_);
                                    crate::leanh::lean_dec_ref(v_inst_1615_);
                                    crate::leanh::lean_dec_ref(v_inst_1614_);
                                    crate::leanh::lean_dec_ref(v_inst_1613_);
                                    crate::leanh::lean_dec_ref(v_inst_1612_);
                                    crate::leanh::lean_dec(v_inst_1611_);
                                    v_n_1621_ = v_arg_1642_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1643_);
                            crate::leanh::lean_dec_ref(v_arg_1642_);
                            crate::leanh::lean_dec(v___f_1618_);
                            crate::leanh::lean_dec(v_toBind_1617_);
                            crate::leanh::lean_dec(v_asVar_1616_);
                            crate::leanh::lean_dec_ref(v_inst_1615_);
                            crate::leanh::lean_dec_ref(v_inst_1614_);
                            crate::leanh::lean_dec_ref(v_inst_1613_);
                            crate::leanh::lean_dec_ref(v_inst_1612_);
                            crate::leanh::lean_dec(v_inst_1611_);
                            v_n_1621_ = v_arg_1638_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_n_1621_) == 9 {
                    v_a_1622_ = crate::leanh::lean_ctor_get(v_n_1621_, 0);
                    crate::leanh::lean_inc_ref(v_a_1622_);
                    crate::leanh::lean_dec_ref_known(v_n_1621_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1622_) == 0 {
                        crate::leanh::lean_dec_ref(v_e_1609_);
                        crate::leanh::lean_dec(v_toVar_1608_);
                        v_val_1623_ = crate::leanh::lean_ctor_get(v_a_1622_, 0);
                        v_isSharedCheck_1632_ = (!crate::leanh::lean_is_exclusive(v_a_1622_)) as u8;
                        if v_isSharedCheck_1632_ == 0 {
                            v___x_1625_ = v_a_1622_;
                            v_isShared_1626_ = v_isSharedCheck_1632_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1623_);
                            crate::leanh::lean_dec(v_a_1622_);
                            v___x_1625_ = crate::leanh::lean_box(0);
                            v_isShared_1626_ = v_isSharedCheck_1632_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1622_);
                        crate::leanh::lean_dec(v_toPure_1610_);
                        v___x_1633_ = crate::leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                        return v___x_1633_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_n_1621_);
                    crate::leanh::lean_dec(v_toPure_1610_);
                    v___x_1634_ = crate::leanh::lean_apply_1(v_toVar_1608_, v_e_1609_);
                    return v___x_1634_;
                }
            }
            2 => {
                v___x_1627_ = lean_nat_to_int(v_val_1623_);
                if v_isShared_1626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1625_, 0, v___x_1627_);
                    v___x_1629_ = v___x_1625_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1627_);
                    v___x_1629_ = v_reuseFailAlloc_1631_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1630_ = crate::leanh::lean_apply_2(
                    v_toPure_1610_,
                    crate::leanh::lean_box(0),
                    v___x_1629_,
                );
                return v___x_1630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(
    mut v_inst_1704_: *mut crate::leanh::LeanObject,
    mut v_inst_1705_: *mut crate::leanh::LeanObject,
    mut v_inst_1706_: *mut crate::leanh::LeanObject,
    mut v_inst_1707_: *mut crate::leanh::LeanObject,
    mut v_inst_1708_: *mut crate::leanh::LeanObject,
    mut v_toVar_1709_: *mut crate::leanh::LeanObject,
    mut v_asVar_1710_: *mut crate::leanh::LeanObject,
    mut v_e_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1712_ = crate::leanh::lean_ctor_get(v_inst_1706_, 0);
    v_toBind_1713_ = crate::leanh::lean_ctor_get(v_inst_1706_, 1);
    crate::leanh::lean_inc_n(v_toBind_1713_, 2);
    v_toPure_1714_ = crate::leanh::lean_ctor_get(v_toApplicative_1712_, 1);
    crate::leanh::lean_inc_n(v_toPure_1714_, 2);
    crate::leanh::lean_inc_ref(v_e_1711_);
    v___x_1715_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1715_, 0, v_e_1711_);
    crate::leanh::lean_inc(v_inst_1704_);
    v___x_1716_ = crate::leanh::lean_apply_2(v_inst_1704_, crate::leanh::lean_box(0), v___x_1715_);
    v___f_1717_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_1717_, 0, v_toPure_1714_);
    v___f_1718_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10 as *mut core::ffi::c_void, 12, 11);
    crate::leanh::lean_closure_set(v___f_1718_, 0, v_toVar_1709_);
    crate::leanh::lean_closure_set(v___f_1718_, 1, v_e_1711_);
    crate::leanh::lean_closure_set(v___f_1718_, 2, v_toPure_1714_);
    crate::leanh::lean_closure_set(v___f_1718_, 3, v_inst_1704_);
    crate::leanh::lean_closure_set(v___f_1718_, 4, v_inst_1705_);
    crate::leanh::lean_closure_set(v___f_1718_, 5, v_inst_1706_);
    crate::leanh::lean_closure_set(v___f_1718_, 6, v_inst_1707_);
    crate::leanh::lean_closure_set(v___f_1718_, 7, v_inst_1708_);
    crate::leanh::lean_closure_set(v___f_1718_, 8, v_asVar_1710_);
    crate::leanh::lean_closure_set(v___f_1718_, 9, v_toBind_1713_);
    crate::leanh::lean_closure_set(v___f_1718_, 10, v___f_1717_);
    v___x_1719_ = crate::leanh::lean_apply_4(
        v_toBind_1713_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1716_,
        v___f_1718_,
    );
    return v___x_1719_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(
    mut v_toPure_1720_: *mut crate::leanh::LeanObject,
    mut v_inst_1721_: *mut crate::leanh::LeanObject,
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
    mut v_inst_1723_: *mut crate::leanh::LeanObject,
    mut v_inst_1724_: *mut crate::leanh::LeanObject,
    mut v_inst_1725_: *mut crate::leanh::LeanObject,
    mut v_toVar_1726_: *mut crate::leanh::LeanObject,
    mut v_asVar_1727_: *mut crate::leanh::LeanObject,
    mut v_arg_1728_: *mut crate::leanh::LeanObject,
    mut v_toBind_1729_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1731_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1731_, 0, v_____do__lift_1730_);
    crate::leanh::lean_closure_set(v___f_1731_, 1, v_toPure_1720_);
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
    v___x_1733_ = crate::leanh::lean_apply_4(
        v_toBind_1729_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1732_,
        v___f_1731_,
    );
    return v___x_1733_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(
    mut v_m_1734_: *mut crate::leanh::LeanObject,
    mut v_inst_1735_: *mut crate::leanh::LeanObject,
    mut v_inst_1736_: *mut crate::leanh::LeanObject,
    mut v_inst_1737_: *mut crate::leanh::LeanObject,
    mut v_inst_1738_: *mut crate::leanh::LeanObject,
    mut v_inst_1739_: *mut crate::leanh::LeanObject,
    mut v_toVar_1740_: *mut crate::leanh::LeanObject,
    mut v_asVar_1741_: *mut crate::leanh::LeanObject,
    mut v_e_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toPure_1744_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1746_, 0, v_____do__lift_1745_);
    v___x_1747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1746_);
    v___x_1748_ =
        crate::leanh::lean_apply_2(v_toPure_1744_, crate::leanh::lean_box(0), v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(
    mut v_toPure_1749_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1751_, 0, v_____do__lift_1750_);
    v___x_1752_ =
        crate::leanh::lean_apply_2(v_toPure_1749_, crate::leanh::lean_box(0), v___x_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(
    mut v_toPure_1753_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1755_, 0, v_____do__lift_1754_);
    v___x_1756_ =
        crate::leanh::lean_apply_2(v_toPure_1753_, crate::leanh::lean_box(0), v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(
    mut v_inst_1757_: *mut crate::leanh::LeanObject,
    mut v_e_1758_: *mut crate::leanh::LeanObject,
    mut v_toBind_1759_: *mut crate::leanh::LeanObject,
    mut v___f_1760_: *mut crate::leanh::LeanObject,
    mut v_____r_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = crate::leanh::lean_apply_1(v_inst_1757_, v_e_1758_);
    v___x_1763_ = crate::leanh::lean_apply_4(
        v_toBind_1759_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1762_,
        v___f_1760_,
    );
    return v___x_1763_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(
    mut v_inst_1764_: *mut crate::leanh::LeanObject,
    mut v_toBind_1765_: *mut crate::leanh::LeanObject,
    mut v___f_1766_: *mut crate::leanh::LeanObject,
    mut v_inst_1767_: *mut crate::leanh::LeanObject,
    mut v_e_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1765_);
    crate::leanh::lean_inc_ref(v_e_1768_);
    v___f_1769_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1769_, 0, v_inst_1764_);
    crate::leanh::lean_closure_set(v___f_1769_, 1, v_e_1768_);
    crate::leanh::lean_closure_set(v___f_1769_, 2, v_toBind_1765_);
    crate::leanh::lean_closure_set(v___f_1769_, 3, v___f_1766_);
    v___x_1770_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
            v_inst_1767_,
            v_e_1768_,
        );
    v___x_1771_ = crate::leanh::lean_apply_4(
        v_toBind_1765_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1770_,
        v___f_1769_,
    );
    return v___x_1771_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(
    mut v_inst_1772_: *mut crate::leanh::LeanObject,
    mut v_toBind_1773_: *mut crate::leanh::LeanObject,
    mut v___f_1774_: *mut crate::leanh::LeanObject,
    mut v_e_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = crate::leanh::lean_apply_1(v_inst_1772_, v_e_1775_);
    v___x_1777_ = crate::leanh::lean_apply_4(
        v_toBind_1773_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1776_,
        v___f_1774_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(
    mut v_skipVar_1778_: u8,
    mut v_toVar_1779_: *mut crate::leanh::LeanObject,
    mut v_toBind_1780_: *mut crate::leanh::LeanObject,
    mut v___f_1781_: *mut crate::leanh::LeanObject,
    mut v_toPure_1782_: *mut crate::leanh::LeanObject,
    mut v_e_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_skipVar_1778_ == 0 {
        let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1782_);
        v___x_1784_ = crate::leanh::lean_apply_1(v_toVar_1779_, v_e_1783_);
        v___x_1785_ = crate::leanh::lean_apply_4(
            v_toBind_1780_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1784_,
            v___f_1781_,
        );
        return v___x_1785_;
    } else {
        let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_1783_);
        crate::leanh::lean_dec(v___f_1781_);
        crate::leanh::lean_dec(v_toBind_1780_);
        crate::leanh::lean_dec(v_toVar_1779_);
        v___x_1786_ = crate::leanh::lean_box(0);
        v___x_1787_ =
            crate::leanh::lean_apply_2(v_toPure_1782_, crate::leanh::lean_box(0), v___x_1786_);
        return v___x_1787_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(
    mut v_skipVar_1788_: *mut crate::leanh::LeanObject,
    mut v_toVar_1789_: *mut crate::leanh::LeanObject,
    mut v_toBind_1790_: *mut crate::leanh::LeanObject,
    mut v___f_1791_: *mut crate::leanh::LeanObject,
    mut v_toPure_1792_: *mut crate::leanh::LeanObject,
    mut v_e_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipVar_boxed_1794_: u8 = 0;
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_1794_ = (crate::leanh::lean_unbox(v_skipVar_1788_) as u8);
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
    mut v_toTopVar_1796_: *mut crate::leanh::LeanObject,
    mut v_e_1797_: *mut crate::leanh::LeanObject,
    mut v_____r_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = crate::leanh::lean_apply_1(v_toTopVar_1796_, v_e_1797_);
    return v___x_1799_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(
    mut v_toTopVar_1800_: *mut crate::leanh::LeanObject,
    mut v_inst_1801_: *mut crate::leanh::LeanObject,
    mut v_toBind_1802_: *mut crate::leanh::LeanObject,
    mut v_e_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_1803_);
    v___f_1804_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1804_, 0, v_toTopVar_1800_);
    crate::leanh::lean_closure_set(v___f_1804_, 1, v_e_1803_);
    v___x_1805_ =
        l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(
            v_inst_1801_,
            v_e_1803_,
        );
    v___x_1806_ = crate::leanh::lean_apply_4(
        v_toBind_1802_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1805_,
        v___f_1804_,
    );
    return v___x_1806_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(
    mut v_____do__lift_1807_: *mut crate::leanh::LeanObject,
    mut v_toPure_1808_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1810_, 0, v_____do__lift_1807_);
    crate::leanh::lean_ctor_set(v___x_1810_, 1, v_____do__lift_1809_);
    v___x_1811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    v___x_1812_ =
        crate::leanh::lean_apply_2(v_toPure_1808_, crate::leanh::lean_box(0), v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(
    mut v_toPure_1813_: *mut crate::leanh::LeanObject,
    mut v_inst_1814_: *mut crate::leanh::LeanObject,
    mut v_inst_1815_: *mut crate::leanh::LeanObject,
    mut v_inst_1816_: *mut crate::leanh::LeanObject,
    mut v_inst_1817_: *mut crate::leanh::LeanObject,
    mut v_inst_1818_: *mut crate::leanh::LeanObject,
    mut v_toVar_1819_: *mut crate::leanh::LeanObject,
    mut v_asVar_1820_: *mut crate::leanh::LeanObject,
    mut v_arg_1821_: *mut crate::leanh::LeanObject,
    mut v_toBind_1822_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1824_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1824_, 0, v_____do__lift_1823_);
    crate::leanh::lean_closure_set(v___f_1824_, 1, v_toPure_1813_);
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
    v___x_1826_ = crate::leanh::lean_apply_4(
        v_toBind_1822_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1825_,
        v___f_1824_,
    );
    return v___x_1826_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(
    mut v_asTopVar_1827_: *mut crate::leanh::LeanObject,
    mut v_e_1828_: *mut crate::leanh::LeanObject,
    mut v_inst_1829_: *mut crate::leanh::LeanObject,
    mut v_inst_1830_: *mut crate::leanh::LeanObject,
    mut v_inst_1831_: *mut crate::leanh::LeanObject,
    mut v_inst_1832_: *mut crate::leanh::LeanObject,
    mut v_inst_1833_: *mut crate::leanh::LeanObject,
    mut v_toVar_1834_: *mut crate::leanh::LeanObject,
    mut v_asVar_1835_: *mut crate::leanh::LeanObject,
    mut v_arg_1836_: *mut crate::leanh::LeanObject,
    mut v_toBind_1837_: *mut crate::leanh::LeanObject,
    mut v___f_1838_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1839_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1839_ == 0 {
        let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1838_);
        crate::leanh::lean_dec(v_toBind_1837_);
        crate::leanh::lean_dec_ref(v_arg_1836_);
        crate::leanh::lean_dec(v_asVar_1835_);
        crate::leanh::lean_dec(v_toVar_1834_);
        crate::leanh::lean_dec_ref(v_inst_1833_);
        crate::leanh::lean_dec_ref(v_inst_1832_);
        crate::leanh::lean_dec_ref(v_inst_1831_);
        crate::leanh::lean_dec_ref(v_inst_1830_);
        crate::leanh::lean_dec(v_inst_1829_);
        v___x_1840_ = crate::leanh::lean_apply_1(v_asTopVar_1827_, v_e_1828_);
        return v___x_1840_;
    } else {
        let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_1828_);
        crate::leanh::lean_dec(v_asTopVar_1827_);
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
        v___x_1842_ = crate::leanh::lean_apply_4(
            v_toBind_1837_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1841_,
            v___f_1838_,
        );
        return v___x_1842_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(
    mut v_asTopVar_1843_: *mut crate::leanh::LeanObject,
    mut v_e_1844_: *mut crate::leanh::LeanObject,
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_inst_1846_: *mut crate::leanh::LeanObject,
    mut v_inst_1847_: *mut crate::leanh::LeanObject,
    mut v_inst_1848_: *mut crate::leanh::LeanObject,
    mut v_inst_1849_: *mut crate::leanh::LeanObject,
    mut v_toVar_1850_: *mut crate::leanh::LeanObject,
    mut v_asVar_1851_: *mut crate::leanh::LeanObject,
    mut v_arg_1852_: *mut crate::leanh::LeanObject,
    mut v_toBind_1853_: *mut crate::leanh::LeanObject,
    mut v___f_1854_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_4902__boxed_1856_: u8 = 0;
    let mut v_res_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4902__boxed_1856_ = (crate::leanh::lean_unbox(v_____do__lift_1855_) as u8);
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
    mut v_____do__lift_1858_: *mut crate::leanh::LeanObject,
    mut v_toPure_1859_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1861_, 0, v_____do__lift_1858_);
    crate::leanh::lean_ctor_set(v___x_1861_, 1, v_____do__lift_1860_);
    v___x_1862_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    v___x_1863_ =
        crate::leanh::lean_apply_2(v_toPure_1859_, crate::leanh::lean_box(0), v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(
    mut v_toPure_1864_: *mut crate::leanh::LeanObject,
    mut v_inst_1865_: *mut crate::leanh::LeanObject,
    mut v_inst_1866_: *mut crate::leanh::LeanObject,
    mut v_inst_1867_: *mut crate::leanh::LeanObject,
    mut v_inst_1868_: *mut crate::leanh::LeanObject,
    mut v_inst_1869_: *mut crate::leanh::LeanObject,
    mut v_toVar_1870_: *mut crate::leanh::LeanObject,
    mut v_asVar_1871_: *mut crate::leanh::LeanObject,
    mut v_arg_1872_: *mut crate::leanh::LeanObject,
    mut v_toBind_1873_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1875_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1875_, 0, v_____do__lift_1874_);
    crate::leanh::lean_closure_set(v___f_1875_, 1, v_toPure_1864_);
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
    v___x_1877_ = crate::leanh::lean_apply_4(
        v_toBind_1873_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1876_,
        v___f_1875_,
    );
    return v___x_1877_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(
    mut v_____do__lift_1878_: *mut crate::leanh::LeanObject,
    mut v_toPure_1879_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1881_, 0, v_____do__lift_1878_);
    crate::leanh::lean_ctor_set(v___x_1881_, 1, v_____do__lift_1880_);
    v___x_1882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
    v___x_1883_ =
        crate::leanh::lean_apply_2(v_toPure_1879_, crate::leanh::lean_box(0), v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(
    mut v_toPure_1884_: *mut crate::leanh::LeanObject,
    mut v_inst_1885_: *mut crate::leanh::LeanObject,
    mut v_inst_1886_: *mut crate::leanh::LeanObject,
    mut v_inst_1887_: *mut crate::leanh::LeanObject,
    mut v_inst_1888_: *mut crate::leanh::LeanObject,
    mut v_inst_1889_: *mut crate::leanh::LeanObject,
    mut v_toVar_1890_: *mut crate::leanh::LeanObject,
    mut v_asVar_1891_: *mut crate::leanh::LeanObject,
    mut v_arg_1892_: *mut crate::leanh::LeanObject,
    mut v_toBind_1893_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1895_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1895_, 0, v_____do__lift_1894_);
    crate::leanh::lean_closure_set(v___f_1895_, 1, v_toPure_1884_);
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
    v___x_1897_ = crate::leanh::lean_apply_4(
        v_toBind_1893_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1896_,
        v___f_1895_,
    );
    return v___x_1897_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(
    mut v_val_1898_: *mut crate::leanh::LeanObject,
    mut v_toPure_1899_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1901_, 0, v_____do__lift_1900_);
    crate::leanh::lean_ctor_set(v___x_1901_, 1, v_val_1898_);
    v___x_1902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1902_, 0, v___x_1901_);
    v___x_1903_ =
        crate::leanh::lean_apply_2(v_toPure_1899_, crate::leanh::lean_box(0), v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(
    mut v_asTopVar_1904_: *mut crate::leanh::LeanObject,
    mut v_e_1905_: *mut crate::leanh::LeanObject,
    mut v_arg_1906_: *mut crate::leanh::LeanObject,
    mut v_toPure_1907_: *mut crate::leanh::LeanObject,
    mut v_toTopVar_1908_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1909_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1909_ == 0 {
                    crate::leanh::lean_dec(v_toTopVar_1908_);
                    crate::leanh::lean_dec(v_toPure_1907_);
                    crate::leanh::lean_dec_ref(v_arg_1906_);
                    v___x_1910_ = crate::leanh::lean_apply_1(v_asTopVar_1904_, v_e_1905_);
                    return v___x_1910_;
                } else {
                    crate::leanh::lean_dec(v_asTopVar_1904_);
                    v___x_1911_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_1906_);
                    if crate::leanh::lean_obj_tag(v___x_1911_) == 1 {
                        crate::leanh::lean_dec(v_toTopVar_1908_);
                        crate::leanh::lean_dec_ref(v_e_1905_);
                        v_val_1912_ = crate::leanh::lean_ctor_get(v___x_1911_, 0);
                        v_isSharedCheck_1921_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1911_)) as u8;
                        if v_isSharedCheck_1921_ == 0 {
                            v___x_1914_ = v___x_1911_;
                            v_isShared_1915_ = v_isSharedCheck_1921_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1912_);
                            crate::leanh::lean_dec(v___x_1911_);
                            v___x_1914_ = crate::leanh::lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1921_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1911_);
                        crate::leanh::lean_dec(v_toPure_1907_);
                        v___x_1922_ = crate::leanh::lean_apply_1(v_toTopVar_1908_, v_e_1905_);
                        return v___x_1922_;
                    }
                }
            }
            1 => {
                v___x_1916_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1916_, 0, v_val_1912_);
                if v_isShared_1915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1916_);
                    v___x_1918_ = v___x_1914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1916_);
                    v___x_1918_ = v_reuseFailAlloc_1920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1919_ = crate::leanh::lean_apply_2(
                    v_toPure_1907_,
                    crate::leanh::lean_box(0),
                    v___x_1918_,
                );
                return v___x_1919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(
    mut v_asTopVar_1923_: *mut crate::leanh::LeanObject,
    mut v_e_1924_: *mut crate::leanh::LeanObject,
    mut v_arg_1925_: *mut crate::leanh::LeanObject,
    mut v_toPure_1926_: *mut crate::leanh::LeanObject,
    mut v_toTopVar_1927_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_4996__boxed_1929_: u8 = 0;
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_4996__boxed_1929_ = (crate::leanh::lean_unbox(v_____do__lift_1928_) as u8);
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
    mut v_asTopVar_1931_: *mut crate::leanh::LeanObject,
    mut v_e_1932_: *mut crate::leanh::LeanObject,
    mut v_arg_1933_: *mut crate::leanh::LeanObject,
    mut v_toPure_1934_: *mut crate::leanh::LeanObject,
    mut v_toTopVar_1935_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1936_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_1936_ == 0 {
                    crate::leanh::lean_dec(v_toTopVar_1935_);
                    crate::leanh::lean_dec(v_toPure_1934_);
                    crate::leanh::lean_dec_ref(v_arg_1933_);
                    v___x_1937_ = crate::leanh::lean_apply_1(v_asTopVar_1931_, v_e_1932_);
                    return v___x_1937_;
                } else {
                    crate::leanh::lean_dec(v_asTopVar_1931_);
                    v___x_1938_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1933_);
                    if crate::leanh::lean_obj_tag(v___x_1938_) == 1 {
                        crate::leanh::lean_dec(v_toTopVar_1935_);
                        crate::leanh::lean_dec_ref(v_e_1932_);
                        v_val_1939_ = crate::leanh::lean_ctor_get(v___x_1938_, 0);
                        v_isSharedCheck_1948_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1938_)) as u8;
                        if v_isSharedCheck_1948_ == 0 {
                            v___x_1941_ = v___x_1938_;
                            v_isShared_1942_ = v_isSharedCheck_1948_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1939_);
                            crate::leanh::lean_dec(v___x_1938_);
                            v___x_1941_ = crate::leanh::lean_box(0);
                            v_isShared_1942_ = v_isSharedCheck_1948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1938_);
                        crate::leanh::lean_dec(v_toPure_1934_);
                        v___x_1949_ = crate::leanh::lean_apply_1(v_toTopVar_1935_, v_e_1932_);
                        return v___x_1949_;
                    }
                }
            }
            1 => {
                v___x_1943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1943_, 0, v_val_1939_);
                if v_isShared_1942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1941_, 0, v___x_1943_);
                    v___x_1945_ = v___x_1941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1943_);
                    v___x_1945_ = v_reuseFailAlloc_1947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1946_ = crate::leanh::lean_apply_2(
                    v_toPure_1934_,
                    crate::leanh::lean_box(0),
                    v___x_1945_,
                );
                return v___x_1946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(
    mut v_asTopVar_1950_: *mut crate::leanh::LeanObject,
    mut v_e_1951_: *mut crate::leanh::LeanObject,
    mut v_arg_1952_: *mut crate::leanh::LeanObject,
    mut v_toPure_1953_: *mut crate::leanh::LeanObject,
    mut v_toTopVar_1954_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_5028__boxed_1956_: u8 = 0;
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_5028__boxed_1956_ = (crate::leanh::lean_unbox(v_____do__lift_1955_) as u8);
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
    mut v_toTopVar_1958_: *mut crate::leanh::LeanObject,
    mut v_e_1959_: *mut crate::leanh::LeanObject,
    mut v_toPure_1960_: *mut crate::leanh::LeanObject,
    mut v_inst_1961_: *mut crate::leanh::LeanObject,
    mut v_inst_1962_: *mut crate::leanh::LeanObject,
    mut v_inst_1963_: *mut crate::leanh::LeanObject,
    mut v_inst_1964_: *mut crate::leanh::LeanObject,
    mut v_inst_1965_: *mut crate::leanh::LeanObject,
    mut v_toVar_1966_: *mut crate::leanh::LeanObject,
    mut v_asVar_1967_: *mut crate::leanh::LeanObject,
    mut v_toBind_1968_: *mut crate::leanh::LeanObject,
    mut v_asTopVar_1969_: *mut crate::leanh::LeanObject,
    mut v___f_1970_: *mut crate::leanh::LeanObject,
    mut v_____x_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: u8 = 0;
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1972_ = l_Lean_Expr_cleanupAnnotations(v_____x_1971_);
                v___x_1973_ = l_Lean_Expr_isApp(v___x_1972_);
                if v___x_1973_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1972_);
                    crate::leanh::lean_dec(v___f_1970_);
                    crate::leanh::lean_dec(v_asTopVar_1969_);
                    crate::leanh::lean_dec(v_toBind_1968_);
                    crate::leanh::lean_dec(v_asVar_1967_);
                    crate::leanh::lean_dec(v_toVar_1966_);
                    crate::leanh::lean_dec_ref(v_inst_1965_);
                    crate::leanh::lean_dec_ref(v_inst_1964_);
                    crate::leanh::lean_dec_ref(v_inst_1963_);
                    crate::leanh::lean_dec_ref(v_inst_1962_);
                    crate::leanh::lean_dec(v_inst_1961_);
                    crate::leanh::lean_dec(v_toPure_1960_);
                    v___x_1974_ = crate::leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                    return v___x_1974_;
                } else {
                    v_arg_1975_ = crate::leanh::lean_ctor_get(v___x_1972_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1975_);
                    v___x_1976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1972_);
                    v___x_1977_ = l_Lean_Expr_isApp(v___x_1976_);
                    if v___x_1977_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1976_);
                        crate::leanh::lean_dec_ref(v_arg_1975_);
                        crate::leanh::lean_dec(v___f_1970_);
                        crate::leanh::lean_dec(v_asTopVar_1969_);
                        crate::leanh::lean_dec(v_toBind_1968_);
                        crate::leanh::lean_dec(v_asVar_1967_);
                        crate::leanh::lean_dec(v_toVar_1966_);
                        crate::leanh::lean_dec_ref(v_inst_1965_);
                        crate::leanh::lean_dec_ref(v_inst_1964_);
                        crate::leanh::lean_dec_ref(v_inst_1963_);
                        crate::leanh::lean_dec_ref(v_inst_1962_);
                        crate::leanh::lean_dec(v_inst_1961_);
                        crate::leanh::lean_dec(v_toPure_1960_);
                        v___x_1978_ = crate::leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                        return v___x_1978_;
                    } else {
                        v_arg_1979_ = crate::leanh::lean_ctor_get(v___x_1976_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1979_);
                        v___x_1980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1976_);
                        v___x_1981_ = l_Lean_Expr_isApp(v___x_1980_);
                        if v___x_1981_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1980_);
                            crate::leanh::lean_dec_ref(v_arg_1979_);
                            crate::leanh::lean_dec_ref(v_arg_1975_);
                            crate::leanh::lean_dec(v___f_1970_);
                            crate::leanh::lean_dec(v_asTopVar_1969_);
                            crate::leanh::lean_dec(v_toBind_1968_);
                            crate::leanh::lean_dec(v_asVar_1967_);
                            crate::leanh::lean_dec(v_toVar_1966_);
                            crate::leanh::lean_dec_ref(v_inst_1965_);
                            crate::leanh::lean_dec_ref(v_inst_1964_);
                            crate::leanh::lean_dec_ref(v_inst_1963_);
                            crate::leanh::lean_dec_ref(v_inst_1962_);
                            crate::leanh::lean_dec(v_inst_1961_);
                            crate::leanh::lean_dec(v_toPure_1960_);
                            v___x_1982_ = crate::leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                            return v___x_1982_;
                        } else {
                            v_arg_1983_ = crate::leanh::lean_ctor_get(v___x_1980_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1983_);
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
                                            crate::leanh::lean_dec(v___f_1970_);
                                            v___x_1993_ = l_Lean_Expr_isApp(v___x_1984_);
                                            if v___x_1993_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_1984_);
                                                crate::leanh::lean_dec_ref(v_arg_1983_);
                                                crate::leanh::lean_dec_ref(v_arg_1979_);
                                                crate::leanh::lean_dec_ref(v_arg_1975_);
                                                crate::leanh::lean_dec(v_asTopVar_1969_);
                                                crate::leanh::lean_dec(v_toBind_1968_);
                                                crate::leanh::lean_dec(v_asVar_1967_);
                                                crate::leanh::lean_dec(v_toVar_1966_);
                                                crate::leanh::lean_dec_ref(v_inst_1965_);
                                                crate::leanh::lean_dec_ref(v_inst_1964_);
                                                crate::leanh::lean_dec_ref(v_inst_1963_);
                                                crate::leanh::lean_dec_ref(v_inst_1962_);
                                                crate::leanh::lean_dec(v_inst_1961_);
                                                crate::leanh::lean_dec(v_toPure_1960_);
                                                v___x_1994_ = crate::leanh::lean_apply_1(
                                                    v_toTopVar_1958_,
                                                    v_e_1959_,
                                                );
                                                return v___x_1994_;
                                            } else {
                                                v___x_1995_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_1984_);
                                                v___x_1996_ = l_Lean_Expr_isApp(v___x_1995_);
                                                if v___x_1996_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_1995_);
                                                    crate::leanh::lean_dec_ref(v_arg_1983_);
                                                    crate::leanh::lean_dec_ref(v_arg_1979_);
                                                    crate::leanh::lean_dec_ref(v_arg_1975_);
                                                    crate::leanh::lean_dec(v_asTopVar_1969_);
                                                    crate::leanh::lean_dec(v_toBind_1968_);
                                                    crate::leanh::lean_dec(v_asVar_1967_);
                                                    crate::leanh::lean_dec(v_toVar_1966_);
                                                    crate::leanh::lean_dec_ref(v_inst_1965_);
                                                    crate::leanh::lean_dec_ref(v_inst_1964_);
                                                    crate::leanh::lean_dec_ref(v_inst_1963_);
                                                    crate::leanh::lean_dec_ref(v_inst_1962_);
                                                    crate::leanh::lean_dec(v_inst_1961_);
                                                    crate::leanh::lean_dec(v_toPure_1960_);
                                                    v___x_1997_ = crate::leanh::lean_apply_1(
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
                                                        crate::leanh::lean_dec_ref(v___x_1998_);
                                                        crate::leanh::lean_dec_ref(v_arg_1983_);
                                                        crate::leanh::lean_dec_ref(v_arg_1979_);
                                                        crate::leanh::lean_dec_ref(v_arg_1975_);
                                                        crate::leanh::lean_dec(v_asTopVar_1969_);
                                                        crate::leanh::lean_dec(v_toBind_1968_);
                                                        crate::leanh::lean_dec(v_asVar_1967_);
                                                        crate::leanh::lean_dec(v_toVar_1966_);
                                                        crate::leanh::lean_dec_ref(v_inst_1965_);
                                                        crate::leanh::lean_dec_ref(v_inst_1964_);
                                                        crate::leanh::lean_dec_ref(v_inst_1963_);
                                                        crate::leanh::lean_dec_ref(v_inst_1962_);
                                                        crate::leanh::lean_dec(v_inst_1961_);
                                                        crate::leanh::lean_dec(v_toPure_1960_);
                                                        v___x_2000_ = crate::leanh::lean_apply_1(
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
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2001_,
                                                                    );
                                                                    if v___x_2009_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1983_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1979_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1975_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_asTopVar_1969_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_toBind_1968_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_asVar_1967_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_toVar_1966_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inst_1965_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inst_1964_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inst_1963_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inst_1962_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_inst_1961_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_toPure_1960_,
                                                                        );
                                                                        v___x_2010_ = crate::leanh::lean_apply_1(v_toTopVar_1958_, v_e_1959_);
                                                                        return v___x_2010_;
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_toTopVar_1958_,
                                                                        );
                                                                        crate::leanh::lean_inc_n(
                                                                            v_toBind_1968_,
                                                                            2,
                                                                        );
                                                                        crate::leanh::lean_inc(
                                                                            v_asVar_1967_,
                                                                        );
                                                                        crate::leanh::lean_inc(
                                                                            v_toVar_1966_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1965_, 2);
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1964_, 2);
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1963_, 2);
                                                                        crate::leanh::lean_inc_ref_n(v_inst_1962_, 2);
                                                                        crate::leanh::lean_inc_n(
                                                                            v_inst_1961_,
                                                                            2,
                                                                        );
                                                                        v___f_2011_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10 as *mut core::ffi::c_void, 11, 10);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 0, v_toPure_1960_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 1, v_inst_1961_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 2, v_inst_1962_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 3, v_inst_1963_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 4, v_inst_1964_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 5, v_inst_1965_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 6, v_toVar_1966_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 7, v_asVar_1967_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 8, v_arg_1975_);
                                                                        crate::leanh::lean_closure_set(v___f_2011_, 9, v_toBind_1968_);
                                                                        v___f_2012_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 0, v_asTopVar_1969_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 1, v_e_1959_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 2, v_inst_1961_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 3, v_inst_1962_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 4, v_inst_1963_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 5, v_inst_1964_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 6, v_inst_1965_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 7, v_toVar_1966_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 8, v_asVar_1967_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 9, v_arg_1979_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 10, v_toBind_1968_);
                                                                        crate::leanh::lean_closure_set(v___f_2012_, 11, v___f_2011_);
                                                                        v___x_2013_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                        v___x_2014_ = crate::leanh::lean_apply_4(v_toBind_1968_, crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_2013_, v___f_2012_);
                                                                        return v___x_2014_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2001_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_toTopVar_1958_,
                                                                    );
                                                                    crate::leanh::lean_inc_n(
                                                                        v_toBind_1968_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_asVar_1967_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_toVar_1966_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1965_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1964_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1963_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_ref_n(
                                                                        v_inst_1962_,
                                                                        2,
                                                                    );
                                                                    crate::leanh::lean_inc_n(
                                                                        v_inst_1961_,
                                                                        2,
                                                                    );
                                                                    v___f_2015_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13 as *mut core::ffi::c_void, 11, 10);
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        0,
                                                                        v_toPure_1960_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        1,
                                                                        v_inst_1961_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        2,
                                                                        v_inst_1962_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        3,
                                                                        v_inst_1963_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        4,
                                                                        v_inst_1964_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        5,
                                                                        v_inst_1965_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        6,
                                                                        v_toVar_1966_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        7,
                                                                        v_asVar_1967_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        8,
                                                                        v_arg_1975_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2015_,
                                                                        9,
                                                                        v_toBind_1968_,
                                                                    );
                                                                    v___f_2016_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        0,
                                                                        v_asTopVar_1969_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        1,
                                                                        v_e_1959_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        2,
                                                                        v_inst_1961_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        3,
                                                                        v_inst_1962_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        4,
                                                                        v_inst_1963_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        5,
                                                                        v_inst_1964_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        6,
                                                                        v_inst_1965_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        7,
                                                                        v_toVar_1966_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        8,
                                                                        v_asVar_1967_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        9,
                                                                        v_arg_1979_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        10,
                                                                        v_toBind_1968_,
                                                                    );
                                                                    crate::leanh::lean_closure_set(
                                                                        v___f_2016_,
                                                                        11,
                                                                        v___f_2015_,
                                                                    );
                                                                    v___x_2017_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                    v___x_2018_ =
                                                                        crate::leanh::lean_apply_4(
                                                                            v_toBind_1968_,
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            ),
                                                                            v___x_2017_,
                                                                            v___f_2016_,
                                                                        );
                                                                    return v___x_2018_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2001_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_toTopVar_1958_,
                                                                );
                                                                crate::leanh::lean_inc_n(
                                                                    v_toBind_1968_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_asVar_1967_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_toVar_1966_,
                                                                );
                                                                crate::leanh::lean_inc_ref_n(
                                                                    v_inst_1965_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_inc_ref_n(
                                                                    v_inst_1964_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_inc_ref_n(
                                                                    v_inst_1963_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_inc_ref_n(
                                                                    v_inst_1962_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_inc_n(
                                                                    v_inst_1961_,
                                                                    2,
                                                                );
                                                                v___f_2019_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14 as *mut core::ffi::c_void, 11, 10);
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    0,
                                                                    v_toPure_1960_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    1,
                                                                    v_inst_1961_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    2,
                                                                    v_inst_1962_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    3,
                                                                    v_inst_1963_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    4,
                                                                    v_inst_1964_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    5,
                                                                    v_inst_1965_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    6,
                                                                    v_toVar_1966_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    7,
                                                                    v_asVar_1967_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    8,
                                                                    v_arg_1975_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2019_,
                                                                    9,
                                                                    v_toBind_1968_,
                                                                );
                                                                v___f_2020_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    0,
                                                                    v_asTopVar_1969_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    1,
                                                                    v_e_1959_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    2,
                                                                    v_inst_1961_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    3,
                                                                    v_inst_1962_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    4,
                                                                    v_inst_1963_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    5,
                                                                    v_inst_1964_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    6,
                                                                    v_inst_1965_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    7,
                                                                    v_toVar_1966_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    8,
                                                                    v_asVar_1967_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    9,
                                                                    v_arg_1979_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    10,
                                                                    v_toBind_1968_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2020_,
                                                                    11,
                                                                    v___f_2019_,
                                                                );
                                                                v___x_2021_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                v___x_2022_ =
                                                                    crate::leanh::lean_apply_4(
                                                                        v_toBind_1968_,
                                                                        crate::leanh::lean_box(0),
                                                                        crate::leanh::lean_box(0),
                                                                        v___x_2021_,
                                                                        v___f_2020_,
                                                                    );
                                                                return v___x_2022_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_2001_);
                                                            crate::leanh::lean_dec(
                                                                v_toTopVar_1958_,
                                                            );
                                                            v___x_2023_ =
                                                                l_Lean_Meta_Sym_getNatValue_x3f(
                                                                    v_arg_1975_,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_2023_,
                                                            ) == 1
                                                            {
                                                                v_val_2024_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2023_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_val_2024_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_2023_,
                                                                    1,
                                                                );
                                                                v___f_2025_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17 as *mut core::ffi::c_void, 3, 2);
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2025_,
                                                                    0,
                                                                    v_val_2024_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2025_,
                                                                    1,
                                                                    v_toPure_1960_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_toBind_1968_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_inst_1965_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_inst_1964_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_inst_1963_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_inst_1962_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_inst_1961_,
                                                                );
                                                                v___f_2026_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    0,
                                                                    v_asTopVar_1969_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    1,
                                                                    v_e_1959_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    2,
                                                                    v_inst_1961_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    3,
                                                                    v_inst_1962_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    4,
                                                                    v_inst_1963_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    5,
                                                                    v_inst_1964_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    6,
                                                                    v_inst_1965_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    7,
                                                                    v_toVar_1966_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    8,
                                                                    v_asVar_1967_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    9,
                                                                    v_arg_1979_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    10,
                                                                    v_toBind_1968_,
                                                                );
                                                                crate::leanh::lean_closure_set(
                                                                    v___f_2026_,
                                                                    11,
                                                                    v___f_2025_,
                                                                );
                                                                v___x_2027_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v_arg_1983_);
                                                                v___x_2028_ =
                                                                    crate::leanh::lean_apply_4(
                                                                        v_toBind_1968_,
                                                                        crate::leanh::lean_box(0),
                                                                        crate::leanh::lean_box(0),
                                                                        v___x_2027_,
                                                                        v___f_2026_,
                                                                    );
                                                                return v___x_2028_;
                                                            } else {
                                                                crate::leanh::lean_dec(v___x_2023_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1983_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1979_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_toBind_1968_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_asVar_1967_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_toVar_1966_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_inst_1965_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_inst_1964_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_inst_1963_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_inst_1962_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_inst_1961_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_toPure_1960_,
                                                                );
                                                                v___x_2029_ =
                                                                    crate::leanh::lean_apply_1(
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
                                            crate::leanh::lean_dec_ref(v___x_1984_);
                                            crate::leanh::lean_dec_ref(v_arg_1983_);
                                            crate::leanh::lean_dec(v_toPure_1960_);
                                            crate::leanh::lean_dec(v_toTopVar_1958_);
                                            crate::leanh::lean_inc(v_toBind_1968_);
                                            crate::leanh::lean_inc_ref(v_inst_1965_);
                                            crate::leanh::lean_inc_ref(v_inst_1964_);
                                            crate::leanh::lean_inc_ref(v_inst_1963_);
                                            crate::leanh::lean_inc_ref(v_inst_1962_);
                                            crate::leanh::lean_inc(v_inst_1961_);
                                            v___f_2030_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed as *mut core::ffi::c_void, 13, 12);
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                0,
                                                v_asTopVar_1969_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                1,
                                                v_e_1959_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                2,
                                                v_inst_1961_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                3,
                                                v_inst_1962_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                4,
                                                v_inst_1963_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                5,
                                                v_inst_1964_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                6,
                                                v_inst_1965_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                7,
                                                v_toVar_1966_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                8,
                                                v_asVar_1967_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                9,
                                                v_arg_1975_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2030_,
                                                10,
                                                v_toBind_1968_,
                                            );
                                            crate::leanh::lean_closure_set(
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
                                            v___x_2032_ = crate::leanh::lean_apply_4(
                                                v_toBind_1968_,
                                                crate::leanh::lean_box(0),
                                                crate::leanh::lean_box(0),
                                                v___x_2031_,
                                                v___f_2030_,
                                            );
                                            return v___x_2032_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1984_);
                                        crate::leanh::lean_dec_ref(v_arg_1983_);
                                        crate::leanh::lean_dec(v___f_1970_);
                                        crate::leanh::lean_dec(v_asVar_1967_);
                                        crate::leanh::lean_dec(v_toVar_1966_);
                                        crate::leanh::lean_dec_ref(v_inst_1962_);
                                        v___f_2033_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed as *mut core::ffi::c_void, 6, 5);
                                        crate::leanh::lean_closure_set(
                                            v___f_2033_,
                                            0,
                                            v_asTopVar_1969_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_2033_, 1, v_e_1959_);
                                        crate::leanh::lean_closure_set(v___f_2033_, 2, v_arg_1975_);
                                        crate::leanh::lean_closure_set(
                                            v___f_2033_,
                                            3,
                                            v_toPure_1960_,
                                        );
                                        crate::leanh::lean_closure_set(
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
                                        v___x_2035_ = crate::leanh::lean_apply_4(
                                            v_toBind_1968_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v___x_2034_,
                                            v___f_2033_,
                                        );
                                        return v___x_2035_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1984_);
                                    crate::leanh::lean_dec_ref(v_arg_1983_);
                                    crate::leanh::lean_dec(v___f_1970_);
                                    crate::leanh::lean_dec(v_asVar_1967_);
                                    crate::leanh::lean_dec(v_toVar_1966_);
                                    crate::leanh::lean_dec_ref(v_inst_1962_);
                                    v___f_2036_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed as *mut core::ffi::c_void, 6, 5);
                                    crate::leanh::lean_closure_set(
                                        v___f_2036_,
                                        0,
                                        v_asTopVar_1969_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2036_, 1, v_e_1959_);
                                    crate::leanh::lean_closure_set(v___f_2036_, 2, v_arg_1975_);
                                    crate::leanh::lean_closure_set(v___f_2036_, 3, v_toPure_1960_);
                                    crate::leanh::lean_closure_set(
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
                                    v___x_2038_ = crate::leanh::lean_apply_4(
                                        v_toBind_1968_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_2037_,
                                        v___f_2036_,
                                    );
                                    return v___x_2038_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1984_);
                                crate::leanh::lean_dec_ref(v_arg_1983_);
                                crate::leanh::lean_dec_ref(v_arg_1975_);
                                crate::leanh::lean_dec(v___f_1970_);
                                crate::leanh::lean_dec(v_toBind_1968_);
                                crate::leanh::lean_dec(v_asVar_1967_);
                                crate::leanh::lean_dec(v_toVar_1966_);
                                crate::leanh::lean_dec_ref(v_inst_1965_);
                                crate::leanh::lean_dec_ref(v_inst_1964_);
                                crate::leanh::lean_dec_ref(v_inst_1963_);
                                crate::leanh::lean_dec_ref(v_inst_1962_);
                                crate::leanh::lean_dec(v_inst_1961_);
                                crate::leanh::lean_dec(v_toTopVar_1958_);
                                if crate::leanh::lean_obj_tag(v_arg_1979_) == 9 {
                                    v_a_2039_ = crate::leanh::lean_ctor_get(v_arg_1979_, 0);
                                    crate::leanh::lean_inc_ref(v_a_2039_);
                                    crate::leanh::lean_dec_ref_known(v_arg_1979_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2039_) == 0 {
                                        crate::leanh::lean_dec(v_asTopVar_1969_);
                                        crate::leanh::lean_dec_ref(v_e_1959_);
                                        v_val_2040_ = crate::leanh::lean_ctor_get(v_a_2039_, 0);
                                        v_isSharedCheck_2050_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_2039_)) as u8;
                                        if v_isSharedCheck_2050_ == 0 {
                                            v___x_2042_ = v_a_2039_;
                                            v_isShared_2043_ = v_isSharedCheck_2050_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_val_2040_);
                                            crate::leanh::lean_dec(v_a_2039_);
                                            v___x_2042_ = crate::leanh::lean_box(0);
                                            v_isShared_2043_ = v_isSharedCheck_2050_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_a_2039_);
                                        crate::leanh::lean_dec(v_toPure_1960_);
                                        v___x_2051_ =
                                            crate::leanh::lean_apply_1(v_asTopVar_1969_, v_e_1959_);
                                        return v___x_2051_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_1979_);
                                    crate::leanh::lean_dec(v_toPure_1960_);
                                    v___x_2052_ =
                                        crate::leanh::lean_apply_1(v_asTopVar_1969_, v_e_1959_);
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
                    crate::leanh::lean_ctor_set(v___x_2042_, 0, v___x_2044_);
                    v___x_2046_ = v___x_2042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2044_);
                    v___x_2046_ = v_reuseFailAlloc_2049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                v___x_2048_ = crate::leanh::lean_apply_2(
                    v_toPure_1960_,
                    crate::leanh::lean_box(0),
                    v___x_2047_,
                );
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(
    mut v_inst_2053_: *mut crate::leanh::LeanObject,
    mut v_inst_2054_: *mut crate::leanh::LeanObject,
    mut v_inst_2055_: *mut crate::leanh::LeanObject,
    mut v_inst_2056_: *mut crate::leanh::LeanObject,
    mut v_inst_2057_: *mut crate::leanh::LeanObject,
    mut v_inst_2058_: *mut crate::leanh::LeanObject,
    mut v_inst_2059_: *mut crate::leanh::LeanObject,
    mut v_e_2060_: *mut crate::leanh::LeanObject,
    mut v_skipVar_2061_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asVar_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toVar_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTopVar_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asTopVar_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2062_ = crate::leanh::lean_ctor_get(v_inst_2056_, 0);
    v_toBind_2063_ = crate::leanh::lean_ctor_get(v_inst_2056_, 1);
    crate::leanh::lean_inc_n(v_toBind_2063_, 6);
    v_toPure_2064_ = crate::leanh::lean_ctor_get(v_toApplicative_2062_, 1);
    crate::leanh::lean_inc_n(v_toPure_2064_, 5);
    v___f_2065_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2065_, 0, v_toPure_2064_);
    v___f_2066_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2066_, 0, v_toPure_2064_);
    v___f_2067_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2067_, 0, v_toPure_2064_);
    crate::leanh::lean_inc(v_inst_2053_);
    crate::leanh::lean_inc_ref(v___f_2067_);
    crate::leanh::lean_inc(v_inst_2059_);
    v_asVar_2068_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v_asVar_2068_, 0, v_inst_2059_);
    crate::leanh::lean_closure_set(v_asVar_2068_, 1, v_toBind_2063_);
    crate::leanh::lean_closure_set(v_asVar_2068_, 2, v___f_2067_);
    crate::leanh::lean_closure_set(v_asVar_2068_, 3, v_inst_2053_);
    v_toVar_2069_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v_toVar_2069_, 0, v_inst_2059_);
    crate::leanh::lean_closure_set(v_toVar_2069_, 1, v_toBind_2063_);
    crate::leanh::lean_closure_set(v_toVar_2069_, 2, v___f_2067_);
    v___x_2070_ = crate::leanh::lean_box((v_skipVar_2061_) as usize);
    crate::leanh::lean_inc_ref(v_toVar_2069_);
    v_toTopVar_2071_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v_toTopVar_2071_, 0, v___x_2070_);
    crate::leanh::lean_closure_set(v_toTopVar_2071_, 1, v_toVar_2069_);
    crate::leanh::lean_closure_set(v_toTopVar_2071_, 2, v_toBind_2063_);
    crate::leanh::lean_closure_set(v_toTopVar_2071_, 3, v___f_2066_);
    crate::leanh::lean_closure_set(v_toTopVar_2071_, 4, v_toPure_2064_);
    crate::leanh::lean_inc_ref(v_toTopVar_2071_);
    v_asTopVar_2072_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v_asTopVar_2072_, 0, v_toTopVar_2071_);
    crate::leanh::lean_closure_set(v_asTopVar_2072_, 1, v_inst_2053_);
    crate::leanh::lean_closure_set(v_asTopVar_2072_, 2, v_toBind_2063_);
    crate::leanh::lean_inc(v_inst_2054_);
    crate::leanh::lean_inc_ref(v_e_2060_);
    v___f_2073_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_2073_, 0, v_toTopVar_2071_);
    crate::leanh::lean_closure_set(v___f_2073_, 1, v_e_2060_);
    crate::leanh::lean_closure_set(v___f_2073_, 2, v_toPure_2064_);
    crate::leanh::lean_closure_set(v___f_2073_, 3, v_inst_2054_);
    crate::leanh::lean_closure_set(v___f_2073_, 4, v_inst_2055_);
    crate::leanh::lean_closure_set(v___f_2073_, 5, v_inst_2056_);
    crate::leanh::lean_closure_set(v___f_2073_, 6, v_inst_2057_);
    crate::leanh::lean_closure_set(v___f_2073_, 7, v_inst_2058_);
    crate::leanh::lean_closure_set(v___f_2073_, 8, v_toVar_2069_);
    crate::leanh::lean_closure_set(v___f_2073_, 9, v_asVar_2068_);
    crate::leanh::lean_closure_set(v___f_2073_, 10, v_toBind_2063_);
    crate::leanh::lean_closure_set(v___f_2073_, 11, v_asTopVar_2072_);
    crate::leanh::lean_closure_set(v___f_2073_, 12, v___f_2065_);
    v___x_2074_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2074_, 0, v_e_2060_);
    v___x_2075_ = crate::leanh::lean_apply_2(v_inst_2054_, crate::leanh::lean_box(0), v___x_2074_);
    v___x_2076_ = crate::leanh::lean_apply_4(
        v_toBind_2063_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2075_,
        v___f_2073_,
    );
    return v___x_2076_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(
    mut v_inst_2077_: *mut crate::leanh::LeanObject,
    mut v_inst_2078_: *mut crate::leanh::LeanObject,
    mut v_inst_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_inst_2082_: *mut crate::leanh::LeanObject,
    mut v_inst_2083_: *mut crate::leanh::LeanObject,
    mut v_e_2084_: *mut crate::leanh::LeanObject,
    mut v_skipVar_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipVar_boxed_2086_: u8 = 0;
    let mut v_res_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_2086_ = (crate::leanh::lean_unbox(v_skipVar_2085_) as u8);
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
    mut v_m_2088_: *mut crate::leanh::LeanObject,
    mut v_inst_2089_: *mut crate::leanh::LeanObject,
    mut v_inst_2090_: *mut crate::leanh::LeanObject,
    mut v_inst_2091_: *mut crate::leanh::LeanObject,
    mut v_inst_2092_: *mut crate::leanh::LeanObject,
    mut v_inst_2093_: *mut crate::leanh::LeanObject,
    mut v_inst_2094_: *mut crate::leanh::LeanObject,
    mut v_inst_2095_: *mut crate::leanh::LeanObject,
    mut v_e_2096_: *mut crate::leanh::LeanObject,
    mut v_skipVar_2097_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_2099_: *mut crate::leanh::LeanObject,
    mut v_inst_2100_: *mut crate::leanh::LeanObject,
    mut v_inst_2101_: *mut crate::leanh::LeanObject,
    mut v_inst_2102_: *mut crate::leanh::LeanObject,
    mut v_inst_2103_: *mut crate::leanh::LeanObject,
    mut v_inst_2104_: *mut crate::leanh::LeanObject,
    mut v_inst_2105_: *mut crate::leanh::LeanObject,
    mut v_inst_2106_: *mut crate::leanh::LeanObject,
    mut v_e_2107_: *mut crate::leanh::LeanObject,
    mut v_skipVar_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipVar_boxed_2109_: u8 = 0;
    let mut v_res_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_2109_ = (crate::leanh::lean_unbox(v_skipVar_2108_) as u8);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0;
    v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
    return v___x_2113_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(
    mut v_inst_2114_: *mut crate::leanh::LeanObject,
    mut v_e_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1);
    v___x_2117_ = l_Lean_indentExpr(v_e_2115_);
    v___x_2118_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2118_, 0, v___x_2116_);
    crate::leanh::lean_ctor_set(v___x_2118_, 1, v___x_2117_);
    v___x_2119_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_reportIssueIfVerbose___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2119_, 0, v___x_2118_);
    v___x_2120_ = crate::leanh::lean_apply_2(v_inst_2114_, crate::leanh::lean_box(0), v___x_2119_);
    return v___x_2120_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(
    mut v_m_2121_: *mut crate::leanh::LeanObject,
    mut v_inst_2122_: *mut crate::leanh::LeanObject,
    mut v_e_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_2122_, v_e_2123_);
    return v___x_2124_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(
    mut v_arg_2125_: *mut crate::leanh::LeanObject,
    mut v_asVar_2126_: *mut crate::leanh::LeanObject,
    mut v_e_2127_: *mut crate::leanh::LeanObject,
    mut v_arg_2128_: *mut crate::leanh::LeanObject,
    mut v_toPure_2129_: *mut crate::leanh::LeanObject,
    mut v_toVar_2130_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2145_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                crate::leanh::lean_dec_ref(v___x_2132_);
                if v___x_2133_ == 0 {
                    crate::leanh::lean_dec(v_toVar_2130_);
                    crate::leanh::lean_dec(v_toPure_2129_);
                    crate::leanh::lean_dec_ref(v_arg_2128_);
                    v___x_2134_ = crate::leanh::lean_apply_1(v_asVar_2126_, v_e_2127_);
                    return v___x_2134_;
                } else {
                    crate::leanh::lean_dec(v_asVar_2126_);
                    v___x_2135_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2128_);
                    if crate::leanh::lean_obj_tag(v___x_2135_) == 1 {
                        crate::leanh::lean_dec(v_toVar_2130_);
                        crate::leanh::lean_dec_ref(v_e_2127_);
                        v_val_2136_ = crate::leanh::lean_ctor_get(v___x_2135_, 0);
                        v_isSharedCheck_2145_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2135_)) as u8;
                        if v_isSharedCheck_2145_ == 0 {
                            v___x_2138_ = v___x_2135_;
                            v_isShared_2139_ = v_isSharedCheck_2145_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2136_);
                            crate::leanh::lean_dec(v___x_2135_);
                            v___x_2138_ = crate::leanh::lean_box(0);
                            v_isShared_2139_ = v_isSharedCheck_2145_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2135_);
                        crate::leanh::lean_dec(v_toPure_2129_);
                        v___x_2146_ = crate::leanh::lean_apply_1(v_toVar_2130_, v_e_2127_);
                        return v___x_2146_;
                    }
                }
            }
            1 => {
                v___x_2140_ = lean_nat_to_int(v_val_2136_);
                if v_isShared_2139_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2138_, 0);
                    crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2140_);
                    v___x_2142_ = v___x_2138_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2140_);
                    v___x_2142_ = v_reuseFailAlloc_2144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2143_ = crate::leanh::lean_apply_2(
                    v_toPure_2129_,
                    crate::leanh::lean_box(0),
                    v___x_2142_,
                );
                return v___x_2143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(
    mut v_arg_2147_: *mut crate::leanh::LeanObject,
    mut v_asVar_2148_: *mut crate::leanh::LeanObject,
    mut v_e_2149_: *mut crate::leanh::LeanObject,
    mut v_arg_2150_: *mut crate::leanh::LeanObject,
    mut v_toPure_2151_: *mut crate::leanh::LeanObject,
    mut v_toVar_2152_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2154_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(v_arg_2147_, v_asVar_2148_, v_e_2149_, v_arg_2150_, v_toPure_2151_, v_toVar_2152_, v_____do__lift_2153_);
    crate::leanh::lean_dec_ref(v_____do__lift_2153_);
    crate::leanh::lean_dec_ref(v_arg_2147_);
    return v_res_2154_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(
    mut v_arg_2155_: *mut crate::leanh::LeanObject,
    mut v_asVar_2156_: *mut crate::leanh::LeanObject,
    mut v_e_2157_: *mut crate::leanh::LeanObject,
    mut v_inst_2158_: *mut crate::leanh::LeanObject,
    mut v_inst_2159_: *mut crate::leanh::LeanObject,
    mut v_inst_2160_: *mut crate::leanh::LeanObject,
    mut v_inst_2161_: *mut crate::leanh::LeanObject,
    mut v_inst_2162_: *mut crate::leanh::LeanObject,
    mut v_toVar_2163_: *mut crate::leanh::LeanObject,
    mut v_arg_2164_: *mut crate::leanh::LeanObject,
    mut v_toBind_2165_: *mut crate::leanh::LeanObject,
    mut v___f_2166_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    v___x_2168_ = l_Lean_Expr_appArg_x21(v_____do__lift_2167_);
    v___x_2169_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2168_,
        v_arg_2155_,
    );
    crate::leanh::lean_dec_ref(v___x_2168_);
    if v___x_2169_ == 0 {
        let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2166_);
        crate::leanh::lean_dec(v_toBind_2165_);
        crate::leanh::lean_dec_ref(v_arg_2164_);
        crate::leanh::lean_dec(v_toVar_2163_);
        crate::leanh::lean_dec_ref(v_inst_2162_);
        crate::leanh::lean_dec_ref(v_inst_2161_);
        crate::leanh::lean_dec_ref(v_inst_2160_);
        crate::leanh::lean_dec_ref(v_inst_2159_);
        crate::leanh::lean_dec(v_inst_2158_);
        v___x_2170_ = crate::leanh::lean_apply_1(v_asVar_2156_, v_e_2157_);
        return v___x_2170_;
    } else {
        let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_2157_);
        v___x_2171_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_2158_, v_inst_2159_, v_inst_2160_, v_inst_2161_, v_inst_2162_, v_toVar_2163_, v_asVar_2156_, v_arg_2164_);
        v___x_2172_ = crate::leanh::lean_apply_4(
            v_toBind_2165_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2171_,
            v___f_2166_,
        );
        return v___x_2172_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(
    mut v_arg_2173_: *mut crate::leanh::LeanObject,
    mut v_asVar_2174_: *mut crate::leanh::LeanObject,
    mut v_e_2175_: *mut crate::leanh::LeanObject,
    mut v_inst_2176_: *mut crate::leanh::LeanObject,
    mut v_inst_2177_: *mut crate::leanh::LeanObject,
    mut v_inst_2178_: *mut crate::leanh::LeanObject,
    mut v_inst_2179_: *mut crate::leanh::LeanObject,
    mut v_inst_2180_: *mut crate::leanh::LeanObject,
    mut v_toVar_2181_: *mut crate::leanh::LeanObject,
    mut v_arg_2182_: *mut crate::leanh::LeanObject,
    mut v_toBind_2183_: *mut crate::leanh::LeanObject,
    mut v___f_2184_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2186_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(v_arg_2173_, v_asVar_2174_, v_e_2175_, v_inst_2176_, v_inst_2177_, v_inst_2178_, v_inst_2179_, v_inst_2180_, v_toVar_2181_, v_arg_2182_, v_toBind_2183_, v___f_2184_, v_____do__lift_2185_);
    crate::leanh::lean_dec_ref(v_____do__lift_2185_);
    crate::leanh::lean_dec_ref(v_arg_2173_);
    return v_res_2186_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(
    mut v_toPure_2187_: *mut crate::leanh::LeanObject,
    mut v_inst_2188_: *mut crate::leanh::LeanObject,
    mut v_inst_2189_: *mut crate::leanh::LeanObject,
    mut v_inst_2190_: *mut crate::leanh::LeanObject,
    mut v_inst_2191_: *mut crate::leanh::LeanObject,
    mut v_inst_2192_: *mut crate::leanh::LeanObject,
    mut v_toVar_2193_: *mut crate::leanh::LeanObject,
    mut v_asVar_2194_: *mut crate::leanh::LeanObject,
    mut v_arg_2195_: *mut crate::leanh::LeanObject,
    mut v_toBind_2196_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2198_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_2198_, 0, v_____do__lift_2197_);
    crate::leanh::lean_closure_set(v___f_2198_, 1, v_toPure_2187_);
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
    v___x_2200_ = crate::leanh::lean_apply_4(
        v_toBind_2196_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2199_,
        v___f_2198_,
    );
    return v___x_2200_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(
    mut v_toVar_2201_: *mut crate::leanh::LeanObject,
    mut v_e_2202_: *mut crate::leanh::LeanObject,
    mut v_toPure_2203_: *mut crate::leanh::LeanObject,
    mut v_inst_2204_: *mut crate::leanh::LeanObject,
    mut v_inst_2205_: *mut crate::leanh::LeanObject,
    mut v_inst_2206_: *mut crate::leanh::LeanObject,
    mut v_inst_2207_: *mut crate::leanh::LeanObject,
    mut v_inst_2208_: *mut crate::leanh::LeanObject,
    mut v_asVar_2209_: *mut crate::leanh::LeanObject,
    mut v_toBind_2210_: *mut crate::leanh::LeanObject,
    mut v_____x_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2273_: u8 = 0;
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2212_ = l_Lean_Expr_cleanupAnnotations(v_____x_2211_);
                v___x_2213_ = l_Lean_Expr_isApp(v___x_2212_);
                if v___x_2213_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2212_);
                    crate::leanh::lean_dec(v_toBind_2210_);
                    crate::leanh::lean_dec(v_asVar_2209_);
                    crate::leanh::lean_dec_ref(v_inst_2208_);
                    crate::leanh::lean_dec_ref(v_inst_2207_);
                    crate::leanh::lean_dec_ref(v_inst_2206_);
                    crate::leanh::lean_dec_ref(v_inst_2205_);
                    crate::leanh::lean_dec(v_inst_2204_);
                    crate::leanh::lean_dec(v_toPure_2203_);
                    v___x_2214_ = crate::leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                    return v___x_2214_;
                } else {
                    v_arg_2215_ = crate::leanh::lean_ctor_get(v___x_2212_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2215_);
                    v___x_2216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2212_);
                    v___x_2217_ = l_Lean_Expr_isApp(v___x_2216_);
                    if v___x_2217_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2216_);
                        crate::leanh::lean_dec_ref(v_arg_2215_);
                        crate::leanh::lean_dec(v_toBind_2210_);
                        crate::leanh::lean_dec(v_asVar_2209_);
                        crate::leanh::lean_dec_ref(v_inst_2208_);
                        crate::leanh::lean_dec_ref(v_inst_2207_);
                        crate::leanh::lean_dec_ref(v_inst_2206_);
                        crate::leanh::lean_dec_ref(v_inst_2205_);
                        crate::leanh::lean_dec(v_inst_2204_);
                        crate::leanh::lean_dec(v_toPure_2203_);
                        v___x_2218_ = crate::leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                        return v___x_2218_;
                    } else {
                        v_arg_2219_ = crate::leanh::lean_ctor_get(v___x_2216_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2219_);
                        v___x_2220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2216_);
                        v___x_2221_ = l_Lean_Expr_isApp(v___x_2220_);
                        if v___x_2221_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2220_);
                            crate::leanh::lean_dec_ref(v_arg_2219_);
                            crate::leanh::lean_dec_ref(v_arg_2215_);
                            crate::leanh::lean_dec(v_toBind_2210_);
                            crate::leanh::lean_dec(v_asVar_2209_);
                            crate::leanh::lean_dec_ref(v_inst_2208_);
                            crate::leanh::lean_dec_ref(v_inst_2207_);
                            crate::leanh::lean_dec_ref(v_inst_2206_);
                            crate::leanh::lean_dec_ref(v_inst_2205_);
                            crate::leanh::lean_dec(v_inst_2204_);
                            crate::leanh::lean_dec(v_toPure_2203_);
                            v___x_2222_ = crate::leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                            return v___x_2222_;
                        } else {
                            v_arg_2223_ = crate::leanh::lean_ctor_get(v___x_2220_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2223_);
                            v___x_2224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2220_);
                            v___x_2225_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4;
                            v___x_2226_ = l_Lean_Expr_isConstOf(v___x_2224_, v___x_2225_);
                            if v___x_2226_ == 0 {
                                v___x_2227_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7;
                                v___x_2228_ = l_Lean_Expr_isConstOf(v___x_2224_, v___x_2227_);
                                if v___x_2228_ == 0 {
                                    v___x_2229_ = l_Lean_Expr_isApp(v___x_2224_);
                                    if v___x_2229_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2224_);
                                        crate::leanh::lean_dec_ref(v_arg_2223_);
                                        crate::leanh::lean_dec_ref(v_arg_2219_);
                                        crate::leanh::lean_dec_ref(v_arg_2215_);
                                        crate::leanh::lean_dec(v_toBind_2210_);
                                        crate::leanh::lean_dec(v_asVar_2209_);
                                        crate::leanh::lean_dec_ref(v_inst_2208_);
                                        crate::leanh::lean_dec_ref(v_inst_2207_);
                                        crate::leanh::lean_dec_ref(v_inst_2206_);
                                        crate::leanh::lean_dec_ref(v_inst_2205_);
                                        crate::leanh::lean_dec(v_inst_2204_);
                                        crate::leanh::lean_dec(v_toPure_2203_);
                                        v___x_2230_ =
                                            crate::leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                                        return v___x_2230_;
                                    } else {
                                        v___x_2231_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2224_);
                                        v___x_2232_ = l_Lean_Expr_isApp(v___x_2231_);
                                        if v___x_2232_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2231_);
                                            crate::leanh::lean_dec_ref(v_arg_2223_);
                                            crate::leanh::lean_dec_ref(v_arg_2219_);
                                            crate::leanh::lean_dec_ref(v_arg_2215_);
                                            crate::leanh::lean_dec(v_toBind_2210_);
                                            crate::leanh::lean_dec(v_asVar_2209_);
                                            crate::leanh::lean_dec_ref(v_inst_2208_);
                                            crate::leanh::lean_dec_ref(v_inst_2207_);
                                            crate::leanh::lean_dec_ref(v_inst_2206_);
                                            crate::leanh::lean_dec_ref(v_inst_2205_);
                                            crate::leanh::lean_dec(v_inst_2204_);
                                            crate::leanh::lean_dec(v_toPure_2203_);
                                            v___x_2233_ = crate::leanh::lean_apply_1(
                                                v_toVar_2201_,
                                                v_e_2202_,
                                            );
                                            return v___x_2233_;
                                        } else {
                                            v___x_2234_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2231_);
                                            v___x_2235_ = l_Lean_Expr_isApp(v___x_2234_);
                                            if v___x_2235_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_2234_);
                                                crate::leanh::lean_dec_ref(v_arg_2223_);
                                                crate::leanh::lean_dec_ref(v_arg_2219_);
                                                crate::leanh::lean_dec_ref(v_arg_2215_);
                                                crate::leanh::lean_dec(v_toBind_2210_);
                                                crate::leanh::lean_dec(v_asVar_2209_);
                                                crate::leanh::lean_dec_ref(v_inst_2208_);
                                                crate::leanh::lean_dec_ref(v_inst_2207_);
                                                crate::leanh::lean_dec_ref(v_inst_2206_);
                                                crate::leanh::lean_dec_ref(v_inst_2205_);
                                                crate::leanh::lean_dec(v_inst_2204_);
                                                crate::leanh::lean_dec(v_toPure_2203_);
                                                v___x_2236_ = crate::leanh::lean_apply_1(
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
                                                        crate::leanh::lean_dec_ref(v___x_2237_);
                                                        if v___x_2243_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_2223_);
                                                            crate::leanh::lean_dec_ref(v_arg_2219_);
                                                            crate::leanh::lean_dec_ref(v_arg_2215_);
                                                            crate::leanh::lean_dec(v_toBind_2210_);
                                                            crate::leanh::lean_dec(v_asVar_2209_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2208_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2207_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2206_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2205_,
                                                            );
                                                            crate::leanh::lean_dec(v_inst_2204_);
                                                            crate::leanh::lean_dec(v_toPure_2203_);
                                                            v___x_2244_ =
                                                                crate::leanh::lean_apply_1(
                                                                    v_toVar_2201_,
                                                                    v_e_2202_,
                                                                );
                                                            return v___x_2244_;
                                                        } else {
                                                            crate::leanh::lean_inc_n(
                                                                v_toBind_2210_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc(v_asVar_2209_);
                                                            crate::leanh::lean_inc(v_toVar_2201_);
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2208_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2207_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2206_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2205_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_n(
                                                                v_inst_2204_,
                                                                2,
                                                            );
                                                            v___f_2245_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1 as *mut core::ffi::c_void, 11, 10);
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                0,
                                                                v_toPure_2203_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                1,
                                                                v_inst_2204_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                2,
                                                                v_inst_2205_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                3,
                                                                v_inst_2206_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                4,
                                                                v_inst_2207_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                5,
                                                                v_inst_2208_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                6,
                                                                v_toVar_2201_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                7,
                                                                v_asVar_2209_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                8,
                                                                v_arg_2215_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2245_,
                                                                9,
                                                                v_toBind_2210_,
                                                            );
                                                            v___f_2246_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                0,
                                                                v_arg_2223_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                1,
                                                                v_asVar_2209_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                2,
                                                                v_e_2202_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                3,
                                                                v_inst_2204_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                4,
                                                                v_inst_2205_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                5,
                                                                v_inst_2206_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                6,
                                                                v_inst_2207_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                7,
                                                                v_inst_2208_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                8,
                                                                v_toVar_2201_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                9,
                                                                v_arg_2219_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                10,
                                                                v_toBind_2210_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2246_,
                                                                11,
                                                                v___f_2245_,
                                                            );
                                                            v___x_2247_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_);
                                                            v___x_2248_ =
                                                                crate::leanh::lean_apply_4(
                                                                    v_toBind_2210_,
                                                                    crate::leanh::lean_box(0),
                                                                    crate::leanh::lean_box(0),
                                                                    v___x_2247_,
                                                                    v___f_2246_,
                                                                );
                                                            return v___x_2248_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_2237_);
                                                        crate::leanh::lean_inc_n(v_toBind_2210_, 2);
                                                        crate::leanh::lean_inc(v_asVar_2209_);
                                                        crate::leanh::lean_inc(v_toVar_2201_);
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2208_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2207_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2206_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2205_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_n(v_inst_2204_, 2);
                                                        v___f_2249_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3 as *mut core::ffi::c_void, 11, 10);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            0,
                                                            v_toPure_2203_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            1,
                                                            v_inst_2204_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            2,
                                                            v_inst_2205_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            3,
                                                            v_inst_2206_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            4,
                                                            v_inst_2207_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            5,
                                                            v_inst_2208_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            6,
                                                            v_toVar_2201_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            7,
                                                            v_asVar_2209_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            8,
                                                            v_arg_2215_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2249_,
                                                            9,
                                                            v_toBind_2210_,
                                                        );
                                                        v___f_2250_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            0,
                                                            v_arg_2223_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            1,
                                                            v_asVar_2209_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            2,
                                                            v_e_2202_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            3,
                                                            v_inst_2204_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            4,
                                                            v_inst_2205_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            5,
                                                            v_inst_2206_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            6,
                                                            v_inst_2207_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            7,
                                                            v_inst_2208_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            8,
                                                            v_toVar_2201_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            9,
                                                            v_arg_2219_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            10,
                                                            v_toBind_2210_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2250_,
                                                            11,
                                                            v___f_2249_,
                                                        );
                                                        v___x_2251_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_);
                                                        v___x_2252_ = crate::leanh::lean_apply_4(
                                                            v_toBind_2210_,
                                                            crate::leanh::lean_box(0),
                                                            crate::leanh::lean_box(0),
                                                            v___x_2251_,
                                                            v___f_2250_,
                                                        );
                                                        return v___x_2252_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_2237_);
                                                    v___x_2253_ = l_Lean_Meta_Sym_getNatValue_x3f(
                                                        v_arg_2215_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_2253_) == 1
                                                    {
                                                        v_val_2254_ = crate::leanh::lean_ctor_get(
                                                            v___x_2253_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_2254_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2253_,
                                                            1,
                                                        );
                                                        v___f_2255_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9 as *mut core::ffi::c_void, 3, 2);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2255_,
                                                            0,
                                                            v_val_2254_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2255_,
                                                            1,
                                                            v_toPure_2203_,
                                                        );
                                                        crate::leanh::lean_inc(v_toBind_2210_);
                                                        crate::leanh::lean_inc_ref(v_inst_2208_);
                                                        crate::leanh::lean_inc_ref(v_inst_2207_);
                                                        crate::leanh::lean_inc_ref(v_inst_2206_);
                                                        crate::leanh::lean_inc_ref(v_inst_2205_);
                                                        crate::leanh::lean_inc(v_inst_2204_);
                                                        v___f_2256_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            0,
                                                            v_arg_2223_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            1,
                                                            v_asVar_2209_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            2,
                                                            v_e_2202_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            3,
                                                            v_inst_2204_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            4,
                                                            v_inst_2205_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            5,
                                                            v_inst_2206_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            6,
                                                            v_inst_2207_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            7,
                                                            v_inst_2208_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            8,
                                                            v_toVar_2201_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            9,
                                                            v_arg_2219_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            10,
                                                            v_toBind_2210_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2256_,
                                                            11,
                                                            v___f_2255_,
                                                        );
                                                        v___x_2257_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_);
                                                        v___x_2258_ = crate::leanh::lean_apply_4(
                                                            v_toBind_2210_,
                                                            crate::leanh::lean_box(0),
                                                            crate::leanh::lean_box(0),
                                                            v___x_2257_,
                                                            v___f_2256_,
                                                        );
                                                        return v___x_2258_;
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_2253_);
                                                        crate::leanh::lean_dec_ref(v_arg_2223_);
                                                        crate::leanh::lean_dec_ref(v_arg_2219_);
                                                        crate::leanh::lean_dec(v_toBind_2210_);
                                                        crate::leanh::lean_dec(v_asVar_2209_);
                                                        crate::leanh::lean_dec_ref(v_inst_2208_);
                                                        crate::leanh::lean_dec_ref(v_inst_2207_);
                                                        crate::leanh::lean_dec_ref(v_inst_2206_);
                                                        crate::leanh::lean_dec_ref(v_inst_2205_);
                                                        crate::leanh::lean_dec(v_inst_2204_);
                                                        crate::leanh::lean_dec(v_toPure_2203_);
                                                        v___x_2259_ = crate::leanh::lean_apply_1(
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
                                    crate::leanh::lean_dec_ref(v___x_2224_);
                                    crate::leanh::lean_dec_ref(v_arg_2223_);
                                    crate::leanh::lean_dec_ref(v_inst_2205_);
                                    v___f_2260_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed as *mut core::ffi::c_void, 7, 6);
                                    crate::leanh::lean_closure_set(v___f_2260_, 0, v_arg_2219_);
                                    crate::leanh::lean_closure_set(v___f_2260_, 1, v_asVar_2209_);
                                    crate::leanh::lean_closure_set(v___f_2260_, 2, v_e_2202_);
                                    crate::leanh::lean_closure_set(v___f_2260_, 3, v_arg_2215_);
                                    crate::leanh::lean_closure_set(v___f_2260_, 4, v_toPure_2203_);
                                    crate::leanh::lean_closure_set(v___f_2260_, 5, v_toVar_2201_);
                                    v___x_2261_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
                                        v_inst_2204_,
                                        v_inst_2206_,
                                        v_inst_2207_,
                                        v_inst_2208_,
                                    );
                                    v___x_2262_ = crate::leanh::lean_apply_4(
                                        v_toBind_2210_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_2261_,
                                        v___f_2260_,
                                    );
                                    return v___x_2262_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2224_);
                                crate::leanh::lean_dec_ref(v_arg_2223_);
                                crate::leanh::lean_dec_ref(v_arg_2215_);
                                crate::leanh::lean_dec(v_toBind_2210_);
                                crate::leanh::lean_dec(v_asVar_2209_);
                                crate::leanh::lean_dec_ref(v_inst_2208_);
                                crate::leanh::lean_dec_ref(v_inst_2207_);
                                crate::leanh::lean_dec_ref(v_inst_2206_);
                                crate::leanh::lean_dec_ref(v_inst_2205_);
                                crate::leanh::lean_dec(v_inst_2204_);
                                if crate::leanh::lean_obj_tag(v_arg_2219_) == 9 {
                                    v_a_2263_ = crate::leanh::lean_ctor_get(v_arg_2219_, 0);
                                    crate::leanh::lean_inc_ref(v_a_2263_);
                                    crate::leanh::lean_dec_ref_known(v_arg_2219_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2263_) == 0 {
                                        crate::leanh::lean_dec_ref(v_e_2202_);
                                        crate::leanh::lean_dec(v_toVar_2201_);
                                        v_val_2264_ = crate::leanh::lean_ctor_get(v_a_2263_, 0);
                                        v_isSharedCheck_2273_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_2263_)) as u8;
                                        if v_isSharedCheck_2273_ == 0 {
                                            v___x_2266_ = v_a_2263_;
                                            v_isShared_2267_ = v_isSharedCheck_2273_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_val_2264_);
                                            crate::leanh::lean_dec(v_a_2263_);
                                            v___x_2266_ = crate::leanh::lean_box(0);
                                            v_isShared_2267_ = v_isSharedCheck_2273_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_a_2263_);
                                        crate::leanh::lean_dec(v_toPure_2203_);
                                        v___x_2274_ =
                                            crate::leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
                                        return v___x_2274_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2219_);
                                    crate::leanh::lean_dec(v_toPure_2203_);
                                    v___x_2275_ =
                                        crate::leanh::lean_apply_1(v_toVar_2201_, v_e_2202_);
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
                    crate::leanh::lean_ctor_set(v___x_2266_, 0, v___x_2268_);
                    v___x_2270_ = v___x_2266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2272_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2268_);
                    v___x_2270_ = v_reuseFailAlloc_2272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2271_ = crate::leanh::lean_apply_2(
                    v_toPure_2203_,
                    crate::leanh::lean_box(0),
                    v___x_2270_,
                );
                return v___x_2271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(
    mut v_inst_2276_: *mut crate::leanh::LeanObject,
    mut v_inst_2277_: *mut crate::leanh::LeanObject,
    mut v_inst_2278_: *mut crate::leanh::LeanObject,
    mut v_inst_2279_: *mut crate::leanh::LeanObject,
    mut v_inst_2280_: *mut crate::leanh::LeanObject,
    mut v_toVar_2281_: *mut crate::leanh::LeanObject,
    mut v_asVar_2282_: *mut crate::leanh::LeanObject,
    mut v_e_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2284_ = crate::leanh::lean_ctor_get(v_inst_2278_, 0);
    v_toBind_2285_ = crate::leanh::lean_ctor_get(v_inst_2278_, 1);
    crate::leanh::lean_inc_n(v_toBind_2285_, 2);
    v_toPure_2286_ = crate::leanh::lean_ctor_get(v_toApplicative_2284_, 1);
    crate::leanh::lean_inc(v_toPure_2286_);
    crate::leanh::lean_inc_ref(v_e_2283_);
    v___x_2287_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2287_, 0, v_e_2283_);
    crate::leanh::lean_inc(v_inst_2276_);
    v___x_2288_ = crate::leanh::lean_apply_2(v_inst_2276_, crate::leanh::lean_box(0), v___x_2287_);
    v___f_2289_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2 as *mut core::ffi::c_void, 11, 10);
    crate::leanh::lean_closure_set(v___f_2289_, 0, v_toVar_2281_);
    crate::leanh::lean_closure_set(v___f_2289_, 1, v_e_2283_);
    crate::leanh::lean_closure_set(v___f_2289_, 2, v_toPure_2286_);
    crate::leanh::lean_closure_set(v___f_2289_, 3, v_inst_2276_);
    crate::leanh::lean_closure_set(v___f_2289_, 4, v_inst_2277_);
    crate::leanh::lean_closure_set(v___f_2289_, 5, v_inst_2278_);
    crate::leanh::lean_closure_set(v___f_2289_, 6, v_inst_2279_);
    crate::leanh::lean_closure_set(v___f_2289_, 7, v_inst_2280_);
    crate::leanh::lean_closure_set(v___f_2289_, 8, v_asVar_2282_);
    crate::leanh::lean_closure_set(v___f_2289_, 9, v_toBind_2285_);
    v___x_2290_ = crate::leanh::lean_apply_4(
        v_toBind_2285_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2288_,
        v___f_2289_,
    );
    return v___x_2290_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(
    mut v_toPure_2291_: *mut crate::leanh::LeanObject,
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
    mut v_inst_2293_: *mut crate::leanh::LeanObject,
    mut v_inst_2294_: *mut crate::leanh::LeanObject,
    mut v_inst_2295_: *mut crate::leanh::LeanObject,
    mut v_inst_2296_: *mut crate::leanh::LeanObject,
    mut v_toVar_2297_: *mut crate::leanh::LeanObject,
    mut v_asVar_2298_: *mut crate::leanh::LeanObject,
    mut v_arg_2299_: *mut crate::leanh::LeanObject,
    mut v_toBind_2300_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2302_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_2302_, 0, v_____do__lift_2301_);
    crate::leanh::lean_closure_set(v___f_2302_, 1, v_toPure_2291_);
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
    v___x_2304_ = crate::leanh::lean_apply_4(
        v_toBind_2300_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2303_,
        v___f_2302_,
    );
    return v___x_2304_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(
    mut v_m_2305_: *mut crate::leanh::LeanObject,
    mut v_inst_2306_: *mut crate::leanh::LeanObject,
    mut v_inst_2307_: *mut crate::leanh::LeanObject,
    mut v_inst_2308_: *mut crate::leanh::LeanObject,
    mut v_inst_2309_: *mut crate::leanh::LeanObject,
    mut v_inst_2310_: *mut crate::leanh::LeanObject,
    mut v_toVar_2311_: *mut crate::leanh::LeanObject,
    mut v_asVar_2312_: *mut crate::leanh::LeanObject,
    mut v_e_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2315_: *mut crate::leanh::LeanObject,
    mut v_toBind_2316_: *mut crate::leanh::LeanObject,
    mut v___f_2317_: *mut crate::leanh::LeanObject,
    mut v_inst_2318_: *mut crate::leanh::LeanObject,
    mut v_e_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2316_);
    crate::leanh::lean_inc_ref(v_e_2319_);
    v___f_2320_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2320_, 0, v_inst_2315_);
    crate::leanh::lean_closure_set(v___f_2320_, 1, v_e_2319_);
    crate::leanh::lean_closure_set(v___f_2320_, 2, v_toBind_2316_);
    crate::leanh::lean_closure_set(v___f_2320_, 3, v___f_2317_);
    v___x_2321_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_2318_, v_e_2319_);
    v___x_2322_ = crate::leanh::lean_apply_4(
        v_toBind_2316_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2321_,
        v___f_2320_,
    );
    return v___x_2322_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(
    mut v_toVar_2323_: *mut crate::leanh::LeanObject,
    mut v_toBind_2324_: *mut crate::leanh::LeanObject,
    mut v___f_2325_: *mut crate::leanh::LeanObject,
    mut v_e_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = crate::leanh::lean_apply_1(v_toVar_2323_, v_e_2326_);
    v___x_2328_ = crate::leanh::lean_apply_4(
        v_toBind_2324_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2327_,
        v___f_2325_,
    );
    return v___x_2328_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(
    mut v_toTopVar_2329_: *mut crate::leanh::LeanObject,
    mut v_inst_2330_: *mut crate::leanh::LeanObject,
    mut v_toBind_2331_: *mut crate::leanh::LeanObject,
    mut v_e_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2332_);
    v___f_2333_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2333_, 0, v_toTopVar_2329_);
    crate::leanh::lean_closure_set(v___f_2333_, 1, v_e_2332_);
    v___x_2334_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_2330_, v_e_2332_);
    v___x_2335_ = crate::leanh::lean_apply_4(
        v_toBind_2331_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2334_,
        v___f_2333_,
    );
    return v___x_2335_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(
    mut v_toPure_2336_: *mut crate::leanh::LeanObject,
    mut v_inst_2337_: *mut crate::leanh::LeanObject,
    mut v_inst_2338_: *mut crate::leanh::LeanObject,
    mut v_inst_2339_: *mut crate::leanh::LeanObject,
    mut v_inst_2340_: *mut crate::leanh::LeanObject,
    mut v_inst_2341_: *mut crate::leanh::LeanObject,
    mut v_toVar_2342_: *mut crate::leanh::LeanObject,
    mut v_asVar_2343_: *mut crate::leanh::LeanObject,
    mut v_arg_2344_: *mut crate::leanh::LeanObject,
    mut v_toBind_2345_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2347_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2347_, 0, v_____do__lift_2346_);
    crate::leanh::lean_closure_set(v___f_2347_, 1, v_toPure_2336_);
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
    v___x_2349_ = crate::leanh::lean_apply_4(
        v_toBind_2345_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2348_,
        v___f_2347_,
    );
    return v___x_2349_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(
    mut v_arg_2350_: *mut crate::leanh::LeanObject,
    mut v_asTopVar_2351_: *mut crate::leanh::LeanObject,
    mut v_e_2352_: *mut crate::leanh::LeanObject,
    mut v_inst_2353_: *mut crate::leanh::LeanObject,
    mut v_inst_2354_: *mut crate::leanh::LeanObject,
    mut v_inst_2355_: *mut crate::leanh::LeanObject,
    mut v_inst_2356_: *mut crate::leanh::LeanObject,
    mut v_inst_2357_: *mut crate::leanh::LeanObject,
    mut v_toVar_2358_: *mut crate::leanh::LeanObject,
    mut v_asVar_2359_: *mut crate::leanh::LeanObject,
    mut v_arg_2360_: *mut crate::leanh::LeanObject,
    mut v_toBind_2361_: *mut crate::leanh::LeanObject,
    mut v___f_2362_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    v___x_2364_ = l_Lean_Expr_appArg_x21(v_____do__lift_2363_);
    v___x_2365_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2364_,
        v_arg_2350_,
    );
    crate::leanh::lean_dec_ref(v___x_2364_);
    if v___x_2365_ == 0 {
        let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2362_);
        crate::leanh::lean_dec(v_toBind_2361_);
        crate::leanh::lean_dec_ref(v_arg_2360_);
        crate::leanh::lean_dec(v_asVar_2359_);
        crate::leanh::lean_dec(v_toVar_2358_);
        crate::leanh::lean_dec_ref(v_inst_2357_);
        crate::leanh::lean_dec_ref(v_inst_2356_);
        crate::leanh::lean_dec_ref(v_inst_2355_);
        crate::leanh::lean_dec_ref(v_inst_2354_);
        crate::leanh::lean_dec(v_inst_2353_);
        v___x_2366_ = crate::leanh::lean_apply_1(v_asTopVar_2351_, v_e_2352_);
        return v___x_2366_;
    } else {
        let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_2352_);
        crate::leanh::lean_dec(v_asTopVar_2351_);
        v___x_2367_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_2353_, v_inst_2354_, v_inst_2355_, v_inst_2356_, v_inst_2357_, v_toVar_2358_, v_asVar_2359_, v_arg_2360_);
        v___x_2368_ = crate::leanh::lean_apply_4(
            v_toBind_2361_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2367_,
            v___f_2362_,
        );
        return v___x_2368_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(
    mut v_arg_2369_: *mut crate::leanh::LeanObject,
    mut v_asTopVar_2370_: *mut crate::leanh::LeanObject,
    mut v_e_2371_: *mut crate::leanh::LeanObject,
    mut v_inst_2372_: *mut crate::leanh::LeanObject,
    mut v_inst_2373_: *mut crate::leanh::LeanObject,
    mut v_inst_2374_: *mut crate::leanh::LeanObject,
    mut v_inst_2375_: *mut crate::leanh::LeanObject,
    mut v_inst_2376_: *mut crate::leanh::LeanObject,
    mut v_toVar_2377_: *mut crate::leanh::LeanObject,
    mut v_asVar_2378_: *mut crate::leanh::LeanObject,
    mut v_arg_2379_: *mut crate::leanh::LeanObject,
    mut v_toBind_2380_: *mut crate::leanh::LeanObject,
    mut v___f_2381_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_____do__lift_2382_);
    crate::leanh::lean_dec_ref(v_arg_2369_);
    return v_res_2383_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(
    mut v_toPure_2384_: *mut crate::leanh::LeanObject,
    mut v_inst_2385_: *mut crate::leanh::LeanObject,
    mut v_inst_2386_: *mut crate::leanh::LeanObject,
    mut v_inst_2387_: *mut crate::leanh::LeanObject,
    mut v_inst_2388_: *mut crate::leanh::LeanObject,
    mut v_inst_2389_: *mut crate::leanh::LeanObject,
    mut v_toVar_2390_: *mut crate::leanh::LeanObject,
    mut v_asVar_2391_: *mut crate::leanh::LeanObject,
    mut v_arg_2392_: *mut crate::leanh::LeanObject,
    mut v_toBind_2393_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2395_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2395_, 0, v_____do__lift_2394_);
    crate::leanh::lean_closure_set(v___f_2395_, 1, v_toPure_2384_);
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
    v___x_2397_ = crate::leanh::lean_apply_4(
        v_toBind_2393_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2396_,
        v___f_2395_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(
    mut v_arg_2398_: *mut crate::leanh::LeanObject,
    mut v_asTopVar_2399_: *mut crate::leanh::LeanObject,
    mut v_e_2400_: *mut crate::leanh::LeanObject,
    mut v_arg_2401_: *mut crate::leanh::LeanObject,
    mut v_toPure_2402_: *mut crate::leanh::LeanObject,
    mut v_toTopVar_2403_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                crate::leanh::lean_dec_ref(v___x_2405_);
                if v___x_2406_ == 0 {
                    crate::leanh::lean_dec(v_toTopVar_2403_);
                    crate::leanh::lean_dec(v_toPure_2402_);
                    crate::leanh::lean_dec_ref(v_arg_2401_);
                    v___x_2407_ = crate::leanh::lean_apply_1(v_asTopVar_2399_, v_e_2400_);
                    return v___x_2407_;
                } else {
                    crate::leanh::lean_dec(v_asTopVar_2399_);
                    v___x_2408_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2401_);
                    if crate::leanh::lean_obj_tag(v___x_2408_) == 1 {
                        crate::leanh::lean_dec(v_toTopVar_2403_);
                        crate::leanh::lean_dec_ref(v_e_2400_);
                        v_val_2409_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                        v_isSharedCheck_2419_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2408_)) as u8;
                        if v_isSharedCheck_2419_ == 0 {
                            v___x_2411_ = v___x_2408_;
                            v_isShared_2412_ = v_isSharedCheck_2419_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2409_);
                            crate::leanh::lean_dec(v___x_2408_);
                            v___x_2411_ = crate::leanh::lean_box(0);
                            v_isShared_2412_ = v_isSharedCheck_2419_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2408_);
                        crate::leanh::lean_dec(v_toPure_2402_);
                        v___x_2420_ = crate::leanh::lean_apply_1(v_toTopVar_2403_, v_e_2400_);
                        return v___x_2420_;
                    }
                }
            }
            1 => {
                v___x_2413_ = lean_nat_to_int(v_val_2409_);
                v___x_2414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                if v_isShared_2412_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2411_, 0, v___x_2414_);
                    v___x_2416_ = v___x_2411_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2414_);
                    v___x_2416_ = v_reuseFailAlloc_2418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2417_ = crate::leanh::lean_apply_2(
                    v_toPure_2402_,
                    crate::leanh::lean_box(0),
                    v___x_2416_,
                );
                return v___x_2417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(
    mut v_arg_2421_: *mut crate::leanh::LeanObject,
    mut v_asTopVar_2422_: *mut crate::leanh::LeanObject,
    mut v_e_2423_: *mut crate::leanh::LeanObject,
    mut v_arg_2424_: *mut crate::leanh::LeanObject,
    mut v_toPure_2425_: *mut crate::leanh::LeanObject,
    mut v_toTopVar_2426_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2428_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(
        v_arg_2421_,
        v_asTopVar_2422_,
        v_e_2423_,
        v_arg_2424_,
        v_toPure_2425_,
        v_toTopVar_2426_,
        v_____do__lift_2427_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_2427_);
    crate::leanh::lean_dec_ref(v_arg_2421_);
    return v_res_2428_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(
    mut v_toTopVar_2429_: *mut crate::leanh::LeanObject,
    mut v_e_2430_: *mut crate::leanh::LeanObject,
    mut v_toPure_2431_: *mut crate::leanh::LeanObject,
    mut v_inst_2432_: *mut crate::leanh::LeanObject,
    mut v_inst_2433_: *mut crate::leanh::LeanObject,
    mut v_inst_2434_: *mut crate::leanh::LeanObject,
    mut v_inst_2435_: *mut crate::leanh::LeanObject,
    mut v_inst_2436_: *mut crate::leanh::LeanObject,
    mut v_toVar_2437_: *mut crate::leanh::LeanObject,
    mut v_asVar_2438_: *mut crate::leanh::LeanObject,
    mut v_toBind_2439_: *mut crate::leanh::LeanObject,
    mut v_asTopVar_2440_: *mut crate::leanh::LeanObject,
    mut v_____x_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u8 = 0;
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2442_ = l_Lean_Expr_cleanupAnnotations(v_____x_2441_);
                v___x_2443_ = l_Lean_Expr_isApp(v___x_2442_);
                if v___x_2443_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2442_);
                    crate::leanh::lean_dec(v_asTopVar_2440_);
                    crate::leanh::lean_dec(v_toBind_2439_);
                    crate::leanh::lean_dec(v_asVar_2438_);
                    crate::leanh::lean_dec(v_toVar_2437_);
                    crate::leanh::lean_dec_ref(v_inst_2436_);
                    crate::leanh::lean_dec_ref(v_inst_2435_);
                    crate::leanh::lean_dec_ref(v_inst_2434_);
                    crate::leanh::lean_dec_ref(v_inst_2433_);
                    crate::leanh::lean_dec(v_inst_2432_);
                    crate::leanh::lean_dec(v_toPure_2431_);
                    v___x_2444_ = crate::leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                    return v___x_2444_;
                } else {
                    v_arg_2445_ = crate::leanh::lean_ctor_get(v___x_2442_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2445_);
                    v___x_2446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2442_);
                    v___x_2447_ = l_Lean_Expr_isApp(v___x_2446_);
                    if v___x_2447_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2446_);
                        crate::leanh::lean_dec_ref(v_arg_2445_);
                        crate::leanh::lean_dec(v_asTopVar_2440_);
                        crate::leanh::lean_dec(v_toBind_2439_);
                        crate::leanh::lean_dec(v_asVar_2438_);
                        crate::leanh::lean_dec(v_toVar_2437_);
                        crate::leanh::lean_dec_ref(v_inst_2436_);
                        crate::leanh::lean_dec_ref(v_inst_2435_);
                        crate::leanh::lean_dec_ref(v_inst_2434_);
                        crate::leanh::lean_dec_ref(v_inst_2433_);
                        crate::leanh::lean_dec(v_inst_2432_);
                        crate::leanh::lean_dec(v_toPure_2431_);
                        v___x_2448_ = crate::leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                        return v___x_2448_;
                    } else {
                        v_arg_2449_ = crate::leanh::lean_ctor_get(v___x_2446_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2449_);
                        v___x_2450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2446_);
                        v___x_2451_ = l_Lean_Expr_isApp(v___x_2450_);
                        if v___x_2451_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2450_);
                            crate::leanh::lean_dec_ref(v_arg_2449_);
                            crate::leanh::lean_dec_ref(v_arg_2445_);
                            crate::leanh::lean_dec(v_asTopVar_2440_);
                            crate::leanh::lean_dec(v_toBind_2439_);
                            crate::leanh::lean_dec(v_asVar_2438_);
                            crate::leanh::lean_dec(v_toVar_2437_);
                            crate::leanh::lean_dec_ref(v_inst_2436_);
                            crate::leanh::lean_dec_ref(v_inst_2435_);
                            crate::leanh::lean_dec_ref(v_inst_2434_);
                            crate::leanh::lean_dec_ref(v_inst_2433_);
                            crate::leanh::lean_dec(v_inst_2432_);
                            crate::leanh::lean_dec(v_toPure_2431_);
                            v___x_2452_ = crate::leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                            return v___x_2452_;
                        } else {
                            v_arg_2453_ = crate::leanh::lean_ctor_get(v___x_2450_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2453_);
                            v___x_2454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2450_);
                            v___x_2455_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4;
                            v___x_2456_ = l_Lean_Expr_isConstOf(v___x_2454_, v___x_2455_);
                            if v___x_2456_ == 0 {
                                v___x_2457_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7;
                                v___x_2458_ = l_Lean_Expr_isConstOf(v___x_2454_, v___x_2457_);
                                if v___x_2458_ == 0 {
                                    v___x_2459_ = l_Lean_Expr_isApp(v___x_2454_);
                                    if v___x_2459_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2454_);
                                        crate::leanh::lean_dec_ref(v_arg_2453_);
                                        crate::leanh::lean_dec_ref(v_arg_2449_);
                                        crate::leanh::lean_dec_ref(v_arg_2445_);
                                        crate::leanh::lean_dec(v_asTopVar_2440_);
                                        crate::leanh::lean_dec(v_toBind_2439_);
                                        crate::leanh::lean_dec(v_asVar_2438_);
                                        crate::leanh::lean_dec(v_toVar_2437_);
                                        crate::leanh::lean_dec_ref(v_inst_2436_);
                                        crate::leanh::lean_dec_ref(v_inst_2435_);
                                        crate::leanh::lean_dec_ref(v_inst_2434_);
                                        crate::leanh::lean_dec_ref(v_inst_2433_);
                                        crate::leanh::lean_dec(v_inst_2432_);
                                        crate::leanh::lean_dec(v_toPure_2431_);
                                        v___x_2460_ =
                                            crate::leanh::lean_apply_1(v_toTopVar_2429_, v_e_2430_);
                                        return v___x_2460_;
                                    } else {
                                        v___x_2461_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2454_);
                                        v___x_2462_ = l_Lean_Expr_isApp(v___x_2461_);
                                        if v___x_2462_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2461_);
                                            crate::leanh::lean_dec_ref(v_arg_2453_);
                                            crate::leanh::lean_dec_ref(v_arg_2449_);
                                            crate::leanh::lean_dec_ref(v_arg_2445_);
                                            crate::leanh::lean_dec(v_asTopVar_2440_);
                                            crate::leanh::lean_dec(v_toBind_2439_);
                                            crate::leanh::lean_dec(v_asVar_2438_);
                                            crate::leanh::lean_dec(v_toVar_2437_);
                                            crate::leanh::lean_dec_ref(v_inst_2436_);
                                            crate::leanh::lean_dec_ref(v_inst_2435_);
                                            crate::leanh::lean_dec_ref(v_inst_2434_);
                                            crate::leanh::lean_dec_ref(v_inst_2433_);
                                            crate::leanh::lean_dec(v_inst_2432_);
                                            crate::leanh::lean_dec(v_toPure_2431_);
                                            v___x_2463_ = crate::leanh::lean_apply_1(
                                                v_toTopVar_2429_,
                                                v_e_2430_,
                                            );
                                            return v___x_2463_;
                                        } else {
                                            v___x_2464_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2461_);
                                            v___x_2465_ = l_Lean_Expr_isApp(v___x_2464_);
                                            if v___x_2465_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_2464_);
                                                crate::leanh::lean_dec_ref(v_arg_2453_);
                                                crate::leanh::lean_dec_ref(v_arg_2449_);
                                                crate::leanh::lean_dec_ref(v_arg_2445_);
                                                crate::leanh::lean_dec(v_asTopVar_2440_);
                                                crate::leanh::lean_dec(v_toBind_2439_);
                                                crate::leanh::lean_dec(v_asVar_2438_);
                                                crate::leanh::lean_dec(v_toVar_2437_);
                                                crate::leanh::lean_dec_ref(v_inst_2436_);
                                                crate::leanh::lean_dec_ref(v_inst_2435_);
                                                crate::leanh::lean_dec_ref(v_inst_2434_);
                                                crate::leanh::lean_dec_ref(v_inst_2433_);
                                                crate::leanh::lean_dec(v_inst_2432_);
                                                crate::leanh::lean_dec(v_toPure_2431_);
                                                v___x_2466_ = crate::leanh::lean_apply_1(
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
                                                        crate::leanh::lean_dec_ref(v___x_2467_);
                                                        if v___x_2473_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_2453_);
                                                            crate::leanh::lean_dec_ref(v_arg_2449_);
                                                            crate::leanh::lean_dec_ref(v_arg_2445_);
                                                            crate::leanh::lean_dec(
                                                                v_asTopVar_2440_,
                                                            );
                                                            crate::leanh::lean_dec(v_toBind_2439_);
                                                            crate::leanh::lean_dec(v_asVar_2438_);
                                                            crate::leanh::lean_dec(v_toVar_2437_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2436_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2435_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2434_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_2433_,
                                                            );
                                                            crate::leanh::lean_dec(v_inst_2432_);
                                                            crate::leanh::lean_dec(v_toPure_2431_);
                                                            v___x_2474_ =
                                                                crate::leanh::lean_apply_1(
                                                                    v_toTopVar_2429_,
                                                                    v_e_2430_,
                                                                );
                                                            return v___x_2474_;
                                                        } else {
                                                            crate::leanh::lean_dec(
                                                                v_toTopVar_2429_,
                                                            );
                                                            crate::leanh::lean_inc_n(
                                                                v_toBind_2439_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc(v_asVar_2438_);
                                                            crate::leanh::lean_inc(v_toVar_2437_);
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2436_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2435_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2434_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_inst_2433_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_inc_n(
                                                                v_inst_2432_,
                                                                2,
                                                            );
                                                            v___f_2475_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4 as *mut core::ffi::c_void, 11, 10);
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                0,
                                                                v_toPure_2431_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                1,
                                                                v_inst_2432_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                2,
                                                                v_inst_2433_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                3,
                                                                v_inst_2434_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                4,
                                                                v_inst_2435_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                5,
                                                                v_inst_2436_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                6,
                                                                v_toVar_2437_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                7,
                                                                v_asVar_2438_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                8,
                                                                v_arg_2445_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2475_,
                                                                9,
                                                                v_toBind_2439_,
                                                            );
                                                            v___f_2476_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                0,
                                                                v_arg_2453_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                1,
                                                                v_asTopVar_2440_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                2,
                                                                v_e_2430_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                3,
                                                                v_inst_2432_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                4,
                                                                v_inst_2433_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                5,
                                                                v_inst_2434_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                6,
                                                                v_inst_2435_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                7,
                                                                v_inst_2436_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                8,
                                                                v_toVar_2437_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                9,
                                                                v_asVar_2438_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                10,
                                                                v_arg_2449_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                11,
                                                                v_toBind_2439_,
                                                            );
                                                            crate::leanh::lean_closure_set(
                                                                v___f_2476_,
                                                                12,
                                                                v___f_2475_,
                                                            );
                                                            v___x_2477_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_);
                                                            v___x_2478_ =
                                                                crate::leanh::lean_apply_4(
                                                                    v_toBind_2439_,
                                                                    crate::leanh::lean_box(0),
                                                                    crate::leanh::lean_box(0),
                                                                    v___x_2477_,
                                                                    v___f_2476_,
                                                                );
                                                            return v___x_2478_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_2467_);
                                                        crate::leanh::lean_dec(v_toTopVar_2429_);
                                                        crate::leanh::lean_inc_n(v_toBind_2439_, 2);
                                                        crate::leanh::lean_inc(v_asVar_2438_);
                                                        crate::leanh::lean_inc(v_toVar_2437_);
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2436_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2435_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2434_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_ref_n(
                                                            v_inst_2433_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_n(v_inst_2432_, 2);
                                                        v___f_2479_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6 as *mut core::ffi::c_void, 11, 10);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            0,
                                                            v_toPure_2431_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            1,
                                                            v_inst_2432_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            2,
                                                            v_inst_2433_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            3,
                                                            v_inst_2434_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            4,
                                                            v_inst_2435_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            5,
                                                            v_inst_2436_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            6,
                                                            v_toVar_2437_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            7,
                                                            v_asVar_2438_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            8,
                                                            v_arg_2445_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2479_,
                                                            9,
                                                            v_toBind_2439_,
                                                        );
                                                        v___f_2480_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            0,
                                                            v_arg_2453_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            1,
                                                            v_asTopVar_2440_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            2,
                                                            v_e_2430_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            3,
                                                            v_inst_2432_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            4,
                                                            v_inst_2433_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            5,
                                                            v_inst_2434_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            6,
                                                            v_inst_2435_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            7,
                                                            v_inst_2436_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            8,
                                                            v_toVar_2437_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            9,
                                                            v_asVar_2438_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            10,
                                                            v_arg_2449_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            11,
                                                            v_toBind_2439_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2480_,
                                                            12,
                                                            v___f_2479_,
                                                        );
                                                        v___x_2481_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_);
                                                        v___x_2482_ = crate::leanh::lean_apply_4(
                                                            v_toBind_2439_,
                                                            crate::leanh::lean_box(0),
                                                            crate::leanh::lean_box(0),
                                                            v___x_2481_,
                                                            v___f_2480_,
                                                        );
                                                        return v___x_2482_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_2467_);
                                                    crate::leanh::lean_dec(v_toTopVar_2429_);
                                                    v___x_2483_ = l_Lean_Meta_Sym_getNatValue_x3f(
                                                        v_arg_2445_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_2483_) == 1
                                                    {
                                                        v_val_2484_ = crate::leanh::lean_ctor_get(
                                                            v___x_2483_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_2484_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2483_,
                                                            1,
                                                        );
                                                        v___f_2485_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17 as *mut core::ffi::c_void, 3, 2);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2485_,
                                                            0,
                                                            v_val_2484_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2485_,
                                                            1,
                                                            v_toPure_2431_,
                                                        );
                                                        crate::leanh::lean_inc(v_toBind_2439_);
                                                        crate::leanh::lean_inc_ref(v_inst_2436_);
                                                        crate::leanh::lean_inc_ref(v_inst_2435_);
                                                        crate::leanh::lean_inc_ref(v_inst_2434_);
                                                        crate::leanh::lean_inc_ref(v_inst_2433_);
                                                        crate::leanh::lean_inc(v_inst_2432_);
                                                        v___f_2486_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            0,
                                                            v_arg_2453_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            1,
                                                            v_asTopVar_2440_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            2,
                                                            v_e_2430_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            3,
                                                            v_inst_2432_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            4,
                                                            v_inst_2433_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            5,
                                                            v_inst_2434_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            6,
                                                            v_inst_2435_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            7,
                                                            v_inst_2436_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            8,
                                                            v_toVar_2437_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            9,
                                                            v_asVar_2438_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            10,
                                                            v_arg_2449_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            11,
                                                            v_toBind_2439_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2486_,
                                                            12,
                                                            v___f_2485_,
                                                        );
                                                        v___x_2487_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_);
                                                        v___x_2488_ = crate::leanh::lean_apply_4(
                                                            v_toBind_2439_,
                                                            crate::leanh::lean_box(0),
                                                            crate::leanh::lean_box(0),
                                                            v___x_2487_,
                                                            v___f_2486_,
                                                        );
                                                        return v___x_2488_;
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_2483_);
                                                        crate::leanh::lean_dec_ref(v_arg_2453_);
                                                        crate::leanh::lean_dec_ref(v_arg_2449_);
                                                        crate::leanh::lean_dec(v_asTopVar_2440_);
                                                        crate::leanh::lean_dec(v_toBind_2439_);
                                                        crate::leanh::lean_dec(v_asVar_2438_);
                                                        crate::leanh::lean_dec(v_toVar_2437_);
                                                        crate::leanh::lean_dec_ref(v_inst_2436_);
                                                        crate::leanh::lean_dec_ref(v_inst_2435_);
                                                        crate::leanh::lean_dec_ref(v_inst_2434_);
                                                        crate::leanh::lean_dec_ref(v_inst_2433_);
                                                        crate::leanh::lean_dec(v_inst_2432_);
                                                        crate::leanh::lean_dec_ref(v_e_2430_);
                                                        v___x_2489_ = crate::leanh::lean_box(0);
                                                        v___x_2490_ = crate::leanh::lean_apply_2(
                                                            v_toPure_2431_,
                                                            crate::leanh::lean_box(0),
                                                            v___x_2489_,
                                                        );
                                                        return v___x_2490_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2454_);
                                    crate::leanh::lean_dec_ref(v_arg_2453_);
                                    crate::leanh::lean_dec(v_asVar_2438_);
                                    crate::leanh::lean_dec(v_toVar_2437_);
                                    crate::leanh::lean_dec_ref(v_inst_2433_);
                                    v___f_2491_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed as *mut core::ffi::c_void, 7, 6);
                                    crate::leanh::lean_closure_set(v___f_2491_, 0, v_arg_2449_);
                                    crate::leanh::lean_closure_set(
                                        v___f_2491_,
                                        1,
                                        v_asTopVar_2440_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2491_, 2, v_e_2430_);
                                    crate::leanh::lean_closure_set(v___f_2491_, 3, v_arg_2445_);
                                    crate::leanh::lean_closure_set(v___f_2491_, 4, v_toPure_2431_);
                                    crate::leanh::lean_closure_set(
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
                                    v___x_2493_ = crate::leanh::lean_apply_4(
                                        v_toBind_2439_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_2492_,
                                        v___f_2491_,
                                    );
                                    return v___x_2493_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2454_);
                                crate::leanh::lean_dec_ref(v_arg_2453_);
                                crate::leanh::lean_dec_ref(v_arg_2445_);
                                crate::leanh::lean_dec(v_toBind_2439_);
                                crate::leanh::lean_dec(v_asVar_2438_);
                                crate::leanh::lean_dec(v_toVar_2437_);
                                crate::leanh::lean_dec_ref(v_inst_2436_);
                                crate::leanh::lean_dec_ref(v_inst_2435_);
                                crate::leanh::lean_dec_ref(v_inst_2434_);
                                crate::leanh::lean_dec_ref(v_inst_2433_);
                                crate::leanh::lean_dec(v_inst_2432_);
                                crate::leanh::lean_dec(v_toTopVar_2429_);
                                if crate::leanh::lean_obj_tag(v_arg_2449_) == 9 {
                                    v_a_2494_ = crate::leanh::lean_ctor_get(v_arg_2449_, 0);
                                    crate::leanh::lean_inc_ref(v_a_2494_);
                                    crate::leanh::lean_dec_ref_known(v_arg_2449_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2494_) == 0 {
                                        crate::leanh::lean_dec(v_asTopVar_2440_);
                                        crate::leanh::lean_dec_ref(v_e_2430_);
                                        v_val_2495_ = crate::leanh::lean_ctor_get(v_a_2494_, 0);
                                        v_isSharedCheck_2505_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_2494_)) as u8;
                                        if v_isSharedCheck_2505_ == 0 {
                                            v___x_2497_ = v_a_2494_;
                                            v_isShared_2498_ = v_isSharedCheck_2505_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_val_2495_);
                                            crate::leanh::lean_dec(v_a_2494_);
                                            v___x_2497_ = crate::leanh::lean_box(0);
                                            v_isShared_2498_ = v_isSharedCheck_2505_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_a_2494_);
                                        crate::leanh::lean_dec(v_toPure_2431_);
                                        v___x_2506_ =
                                            crate::leanh::lean_apply_1(v_asTopVar_2440_, v_e_2430_);
                                        return v___x_2506_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2449_);
                                    crate::leanh::lean_dec(v_toPure_2431_);
                                    v___x_2507_ =
                                        crate::leanh::lean_apply_1(v_asTopVar_2440_, v_e_2430_);
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
                    crate::leanh::lean_ctor_set(v___x_2497_, 0, v___x_2499_);
                    v___x_2501_ = v___x_2497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2499_);
                    v___x_2501_ = v_reuseFailAlloc_2504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2502_, 0, v___x_2501_);
                v___x_2503_ = crate::leanh::lean_apply_2(
                    v_toPure_2431_,
                    crate::leanh::lean_box(0),
                    v___x_2502_,
                );
                return v___x_2503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(
    mut v_inst_2508_: *mut crate::leanh::LeanObject,
    mut v_inst_2509_: *mut crate::leanh::LeanObject,
    mut v_inst_2510_: *mut crate::leanh::LeanObject,
    mut v_inst_2511_: *mut crate::leanh::LeanObject,
    mut v_inst_2512_: *mut crate::leanh::LeanObject,
    mut v_inst_2513_: *mut crate::leanh::LeanObject,
    mut v_inst_2514_: *mut crate::leanh::LeanObject,
    mut v_e_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asVar_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toVar_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTopVar_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asTopVar_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2516_ = crate::leanh::lean_ctor_get(v_inst_2511_, 0);
    v_toBind_2517_ = crate::leanh::lean_ctor_get(v_inst_2511_, 1);
    crate::leanh::lean_inc_n(v_toBind_2517_, 6);
    v_toPure_2518_ = crate::leanh::lean_ctor_get(v_toApplicative_2516_, 1);
    crate::leanh::lean_inc_n(v_toPure_2518_, 3);
    v___f_2519_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2519_, 0, v_toPure_2518_);
    v___f_2520_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2520_, 0, v_toPure_2518_);
    crate::leanh::lean_inc(v_inst_2508_);
    crate::leanh::lean_inc_ref(v___f_2520_);
    crate::leanh::lean_inc(v_inst_2514_);
    v_asVar_2521_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v_asVar_2521_, 0, v_inst_2514_);
    crate::leanh::lean_closure_set(v_asVar_2521_, 1, v_toBind_2517_);
    crate::leanh::lean_closure_set(v_asVar_2521_, 2, v___f_2520_);
    crate::leanh::lean_closure_set(v_asVar_2521_, 3, v_inst_2508_);
    v_toVar_2522_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v_toVar_2522_, 0, v_inst_2514_);
    crate::leanh::lean_closure_set(v_toVar_2522_, 1, v_toBind_2517_);
    crate::leanh::lean_closure_set(v_toVar_2522_, 2, v___f_2520_);
    crate::leanh::lean_inc_ref(v_toVar_2522_);
    v_toTopVar_2523_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v_toTopVar_2523_, 0, v_toVar_2522_);
    crate::leanh::lean_closure_set(v_toTopVar_2523_, 1, v_toBind_2517_);
    crate::leanh::lean_closure_set(v_toTopVar_2523_, 2, v___f_2519_);
    crate::leanh::lean_inc_ref(v_toTopVar_2523_);
    v_asTopVar_2524_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v_asTopVar_2524_, 0, v_toTopVar_2523_);
    crate::leanh::lean_closure_set(v_asTopVar_2524_, 1, v_inst_2508_);
    crate::leanh::lean_closure_set(v_asTopVar_2524_, 2, v_toBind_2517_);
    crate::leanh::lean_inc(v_inst_2509_);
    crate::leanh::lean_inc_ref(v_e_2515_);
    v___f_2525_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5 as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_2525_, 0, v_toTopVar_2523_);
    crate::leanh::lean_closure_set(v___f_2525_, 1, v_e_2515_);
    crate::leanh::lean_closure_set(v___f_2525_, 2, v_toPure_2518_);
    crate::leanh::lean_closure_set(v___f_2525_, 3, v_inst_2509_);
    crate::leanh::lean_closure_set(v___f_2525_, 4, v_inst_2510_);
    crate::leanh::lean_closure_set(v___f_2525_, 5, v_inst_2511_);
    crate::leanh::lean_closure_set(v___f_2525_, 6, v_inst_2512_);
    crate::leanh::lean_closure_set(v___f_2525_, 7, v_inst_2513_);
    crate::leanh::lean_closure_set(v___f_2525_, 8, v_toVar_2522_);
    crate::leanh::lean_closure_set(v___f_2525_, 9, v_asVar_2521_);
    crate::leanh::lean_closure_set(v___f_2525_, 10, v_toBind_2517_);
    crate::leanh::lean_closure_set(v___f_2525_, 11, v_asTopVar_2524_);
    v___x_2526_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2526_, 0, v_e_2515_);
    v___x_2527_ = crate::leanh::lean_apply_2(v_inst_2509_, crate::leanh::lean_box(0), v___x_2526_);
    v___x_2528_ = crate::leanh::lean_apply_4(
        v_toBind_2517_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2527_,
        v___f_2525_,
    );
    return v___x_2528_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_reifySemiring_x3f(
    mut v_m_2529_: *mut crate::leanh::LeanObject,
    mut v_inst_2530_: *mut crate::leanh::LeanObject,
    mut v_inst_2531_: *mut crate::leanh::LeanObject,
    mut v_inst_2532_: *mut crate::leanh::LeanObject,
    mut v_inst_2533_: *mut crate::leanh::LeanObject,
    mut v_inst_2534_: *mut crate::leanh::LeanObject,
    mut v_inst_2535_: *mut crate::leanh::LeanObject,
    mut v_inst_2536_: *mut crate::leanh::LeanObject,
    mut v_e_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Reify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Reify(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Reify(builtin);
}
