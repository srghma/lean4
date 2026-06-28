// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.Basic
// Imports: Std.Data.HashMap Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Lean.Meta.AppBuilder Lean.Data.RArray
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::RArray::{
    initialize_Lean_Data_RArray, l_Lean_RArray_ofArray___redArg, l_Lean_RArray_toExpr___redArg,
    runtime_initialize_Lean_Data_RArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_eqv___boxed,
    l_Lean_Expr_hash, l_Lean_Expr_hash___boxed, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5,
    l_Lean_mkApp6, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [66, 86, 66, 105, 110, 79, 112, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 110, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        8633590422926641219 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [111, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        16739768336988840329 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [120, 111, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        12702694847026093380 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 100, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        14273346465055528428 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 117, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16_value
        ) as *mut crate::leanh::LeanObject,
        5895671572980706882 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19_value:
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
    m_data: [117, 100, 105, 118, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19_value
        ) as *mut crate::leanh::LeanObject,
        10337161908347300449 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22_value:
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
    m_data: [117, 109, 111, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22_value
        ) as *mut crate::leanh::LeanObject,
        799197807962006713 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2052334966301458605 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value:
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
    m_data: [66, 86, 85, 110, 79, 112, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 111, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5396454276475693598 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [114, 111, 116, 97, 116, 101, 76, 101, 102, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9807480938810536989 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7_value:
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
    m_data: [114, 111, 116, 97, 116, 101, 82, 105, 103, 104, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7_value)
            as *mut crate::leanh::LeanObject,
        18013547890344707440 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 67, 111, 110, 115,
        116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        15020990588075728728 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 118, 101, 114, 115, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        13041317507303989844 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [99, 108, 122, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16_value
        ) as *mut crate::leanh::LeanObject,
        744326716584575709 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19_value:
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
    m_data: [99, 112, 111, 112, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19_value
        ) as *mut crate::leanh::LeanObject,
        4313869223568439254 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440452707255258700 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value:
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
    m_data: [66, 86, 69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [118, 97, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10402728041249638302 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11927932611098301909 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value:
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
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value)
            as *mut crate::leanh::LeanObject,
        5394957827732845164 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8_value)
            as *mut crate::leanh::LeanObject,
        7578295756008745317 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 120, 116, 114, 97, 99, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11_value)
            as *mut crate::leanh::LeanObject,
        646477182314419725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [98, 105, 110, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value)
            as *mut crate::leanh::LeanObject,
        1893448420036949551 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [117, 110, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17_value)
            as *mut crate::leanh::LeanObject,
        13103364627973585450 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21_value:
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
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21_value)
            as *mut crate::leanh::LeanObject,
        13480818501600609864 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29_value:
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
    m_data: [97, 112, 112, 101, 110, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29_value)
            as *mut crate::leanh::LeanObject,
        14769465239096254100 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32_value:
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
    m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32_value)
            as *mut crate::leanh::LeanObject,
        11468030476923802729 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35_value:
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
    m_data: [115, 104, 105, 102, 116, 76, 101, 102, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35_value)
            as *mut crate::leanh::LeanObject,
        6896204920017572293 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38_value)
            as *mut crate::leanh::LeanObject,
        16353154075727218503 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41_value)
            as *mut crate::leanh::LeanObject,
        9849265584244012391 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410340039599863083 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value:
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
    m_data: [66, 86, 66, 105, 110, 80, 114, 101, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [101, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14358323385385135839 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        9171839772800810094 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 108, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14358323385385135839 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        6679632329825533760 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14358323385385135839 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value:
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
    m_data: [71, 97, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13347281081598155225 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        8714298000618519999 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13347281081598155225 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        4160575121790354240 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [98, 101, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13347281081598155225 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        14669553018067580624 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13347281081598155225 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        4514021465289239077 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13347281081598155225 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_BVDecide_instToExprGate: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value:
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
    m_data: [66, 86, 80, 114, 101, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18198180362361044236 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value)
            as *mut crate::leanh::LeanObject,
        9369798261105284388 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 101, 116, 76, 115, 98, 68, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18198180362361044236 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3_value)
            as *mut crate::leanh::LeanObject,
        4649274213110965225 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18198180362361044236 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_BVDecide_instToExprBVPred: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 111, 111, 108, 69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [108, 105, 116, 101, 114, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5051218143360974414 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        849521351811639932 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5051218143360974414 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value)
            as *mut crate::leanh::LeanObject,
        7733665888557906164 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        15761733860085307253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        9255189395584251158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5051218143360974414 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15553663127940073204 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15_value:
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
    m_data: [103, 97, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5051218143360974414 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        16066464032356577345 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5051218143360974414 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        5435855234965385182 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value:
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
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5051218143360974414 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0_value: crate::leanh::LeanStringObject<66> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [117, 112, 100, 97, 116, 101, 65, 116, 111, 109, 115, 65, 115, 115, 105, 103, 110, 109, 101, 110, 116, 32, 115, 104, 111, 117, 108, 100, 32, 111, 110, 108, 121, 32, 98, 101, 32, 99, 97, 108, 108, 101, 100, 32, 119, 104, 101, 110, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 97, 110, 32, 97, 116, 111, 109, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 97, 99, 107, 101, 100, 66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value) as *mut crate::leanh::LeanObject,6595781100213770805 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4_value: crate::leanh::LeanClosureObject<6> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*6) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0 as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 6, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [98, 118, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0_value)
            as *mut crate::leanh::LeanObject,
        142734480563613395 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15847151208953044930 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1_value)
                as *mut crate::leanh::LeanObject,
            10551690841954068875 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6_value: crate::leanh::LeanStringObject<
    19,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        78, 101, 119, 32, 97, 116, 111, 109, 32, 111, 102, 32, 119, 105, 100, 116, 104, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        44, 32, 115, 121, 110, 116, 104, 101, 116, 105, 99, 63, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12_value: crate::leanh::LeanStringObject<
    40,
> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101,
        99, 105, 100, 101, 46, 82, 101, 102, 108, 101, 99, 116, 46, 66, 97, 115, 105, 99, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13_value: crate::leanh::LeanStringObject<
    35,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101,
        99, 105, 100, 101, 46, 77, 46, 108, 111, 111, 107, 117, 112, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14_value: crate::leanh::LeanStringObject<
    58,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        84, 104, 101, 32, 115, 97, 109, 101, 32, 97, 116, 111, 109, 32, 111, 99, 99, 117, 114, 115,
        32, 119, 105, 116, 104, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 119, 105, 100,
        116, 104, 115, 44, 32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 32, 98, 117, 103, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2227_ = crate::leanh::lean_box(0);
    v___x_2228_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5;
    v___x_2229_ = l_Lean_mkConst(v___x_2228_, v___x_2227_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = crate::leanh::lean_box(0);
    v___x_2238_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8;
    v___x_2239_ = l_Lean_mkConst(v___x_2238_, v___x_2237_);
    return v___x_2239_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2247_ = crate::leanh::lean_box(0);
    v___x_2248_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11;
    v___x_2249_ = l_Lean_mkConst(v___x_2248_, v___x_2247_);
    return v___x_2249_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2257_ = crate::leanh::lean_box(0);
    v___x_2258_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14;
    v___x_2259_ = l_Lean_mkConst(v___x_2258_, v___x_2257_);
    return v___x_2259_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = crate::leanh::lean_box(0);
    v___x_2268_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17;
    v___x_2269_ = l_Lean_mkConst(v___x_2268_, v___x_2267_);
    return v___x_2269_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = crate::leanh::lean_box(0);
    v___x_2278_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20;
    v___x_2279_ = l_Lean_mkConst(v___x_2278_, v___x_2277_);
    return v___x_2279_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2287_ = crate::leanh::lean_box(0);
    v___x_2288_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23;
    v___x_2289_ = l_Lean_mkConst(v___x_2288_, v___x_2287_);
    return v___x_2289_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(
    mut v_x_2290_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2290_ {
        0 => {
            let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2291_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6,
            );
            return v___x_2291_;
        }
        1 => {
            let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2292_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9,
            );
            return v___x_2292_;
        }
        2 => {
            let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2293_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12,
            );
            return v___x_2293_;
        }
        3 => {
            let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2294_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15,
            );
            return v___x_2294_;
        }
        4 => {
            let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2295_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18,
            );
            return v___x_2295_;
        }
        5 => {
            let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2296_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21,
            );
            return v___x_2296_;
        }
        _ => {
            let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2297_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24,
            );
            return v___x_2297_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___boxed(
    mut v_x_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2299_: u8 = 0;
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2299_ = (crate::leanh::lean_unbox(v_x_2298_) as u8);
    v_res_2300_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(v_x_boxed_2299_);
    return v_res_2300_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = crate::leanh::lean_box(0);
    v___x_2308_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1;
    v___x_2309_ = l_Lean_mkConst(v___x_2308_, v___x_2307_);
    return v___x_2309_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2,
    );
    v___f_2311_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0;
    v___x_2312_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2312_, 0, v___f_2311_);
    crate::leanh::lean_ctor_set(v___x_2312_, 1, v___x_2310_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3,
    );
    return v___x_2313_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2322_ = crate::leanh::lean_box(0);
    v___x_2323_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2;
    v___x_2324_ = l_Lean_mkConst(v___x_2323_, v___x_2322_);
    return v___x_2324_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = crate::leanh::lean_box(0);
    v___x_2333_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5;
    v___x_2334_ = l_Lean_mkConst(v___x_2333_, v___x_2332_);
    return v___x_2334_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = crate::leanh::lean_box(0);
    v___x_2343_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8;
    v___x_2344_ = l_Lean_mkConst(v___x_2343_, v___x_2342_);
    return v___x_2344_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2352_ = crate::leanh::lean_box(0);
    v___x_2353_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11;
    v___x_2354_ = l_Lean_mkConst(v___x_2353_, v___x_2352_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2362_ = crate::leanh::lean_box(0);
    v___x_2363_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14;
    v___x_2364_ = l_Lean_mkConst(v___x_2363_, v___x_2362_);
    return v___x_2364_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = crate::leanh::lean_box(0);
    v___x_2373_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17;
    v___x_2374_ = l_Lean_mkConst(v___x_2373_, v___x_2372_);
    return v___x_2374_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = crate::leanh::lean_box(0);
    v___x_2383_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20;
    v___x_2384_ = l_Lean_mkConst(v___x_2383_, v___x_2382_);
    return v___x_2384_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0(
    mut v_x_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2385_) {
        0 => {
            let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2386_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3,
            );
            return v___x_2386_;
        }
        1 => {
            let mut v_n_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_2387_ = crate::leanh::lean_ctor_get(v_x_2385_, 0);
            crate::leanh::lean_inc(v_n_2387_);
            crate::leanh::lean_dec_ref_known(v_x_2385_, 1);
            v___x_2388_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6,
            );
            v___x_2389_ = l_Lean_mkNatLit(v_n_2387_);
            v___x_2390_ = l_Lean_Expr_app___override(v___x_2388_, v___x_2389_);
            return v___x_2390_;
        }
        2 => {
            let mut v_n_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_2391_ = crate::leanh::lean_ctor_get(v_x_2385_, 0);
            crate::leanh::lean_inc(v_n_2391_);
            crate::leanh::lean_dec_ref_known(v_x_2385_, 1);
            v___x_2392_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9,
            );
            v___x_2393_ = l_Lean_mkNatLit(v_n_2391_);
            v___x_2394_ = l_Lean_Expr_app___override(v___x_2392_, v___x_2393_);
            return v___x_2394_;
        }
        3 => {
            let mut v_n_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_2395_ = crate::leanh::lean_ctor_get(v_x_2385_, 0);
            crate::leanh::lean_inc(v_n_2395_);
            crate::leanh::lean_dec_ref_known(v_x_2385_, 1);
            v___x_2396_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12,
            );
            v___x_2397_ = l_Lean_mkNatLit(v_n_2395_);
            v___x_2398_ = l_Lean_Expr_app___override(v___x_2396_, v___x_2397_);
            return v___x_2398_;
        }
        4 => {
            let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2399_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15,
            );
            return v___x_2399_;
        }
        5 => {
            let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2400_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18,
            );
            return v___x_2400_;
        }
        _ => {
            let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2401_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21,
            );
            return v___x_2401_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2408_ = crate::leanh::lean_box(0);
    v___x_2409_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1;
    v___x_2410_ = l_Lean_mkConst(v___x_2409_, v___x_2408_);
    return v___x_2410_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2,
    );
    v___f_2412_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0;
    v___x_2413_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2413_, 0, v___f_2412_);
    crate::leanh::lean_ctor_set(v___x_2413_, 1, v___x_2411_);
    return v___x_2413_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3,
    );
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = crate::leanh::lean_box(0);
    v___x_2424_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2;
    v___x_2425_ = l_Lean_mkConst(v___x_2424_, v___x_2423_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = crate::leanh::lean_box(0);
    v___x_2434_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5;
    v___x_2435_ = l_Lean_mkConst(v___x_2434_, v___x_2433_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = crate::leanh::lean_box(0);
    v___x_2442_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9;
    v___x_2443_ = l_Lean_Expr_const___override(v___x_2442_, v___x_2441_);
    return v___x_2443_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2451_ = crate::leanh::lean_box(0);
    v___x_2452_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12;
    v___x_2453_ = l_Lean_mkConst(v___x_2452_, v___x_2451_);
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = crate::leanh::lean_box(0);
    v___x_2462_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15;
    v___x_2463_ = l_Lean_mkConst(v___x_2462_, v___x_2461_);
    return v___x_2463_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = crate::leanh::lean_box(0);
    v___x_2472_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18;
    v___x_2473_ = l_Lean_mkConst(v___x_2472_, v___x_2471_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2480_ = l_Lean_Level_ofNat(v___x_2479_);
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = crate::leanh::lean_box(0);
    v___x_2482_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23,
    );
    v___x_2483_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
    crate::leanh::lean_ctor_set(v___x_2483_, 1, v___x_2481_);
    return v___x_2483_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24,
    );
    v___x_2485_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22;
    v___x_2486_ = l_Lean_mkConst(v___x_2485_, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = crate::leanh::lean_box(0);
    v___x_2491_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27;
    v___x_2492_ = l_Lean_mkConst(v___x_2491_, v___x_2490_);
    return v___x_2492_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2500_ = crate::leanh::lean_box(0);
    v___x_2501_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30;
    v___x_2502_ = l_Lean_mkConst(v___x_2501_, v___x_2500_);
    return v___x_2502_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = crate::leanh::lean_box(0);
    v___x_2511_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33;
    v___x_2512_ = l_Lean_mkConst(v___x_2511_, v___x_2510_);
    return v___x_2512_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ = crate::leanh::lean_box(0);
    v___x_2521_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36;
    v___x_2522_ = l_Lean_mkConst(v___x_2521_, v___x_2520_);
    return v___x_2522_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = crate::leanh::lean_box(0);
    v___x_2531_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39;
    v___x_2532_ = l_Lean_mkConst(v___x_2531_, v___x_2530_);
    return v___x_2532_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = crate::leanh::lean_box(0);
    v___x_2541_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42;
    v___x_2542_ = l_Lean_mkConst(v___x_2541_, v___x_2540_);
    return v___x_2542_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(
    mut v_w_2543_: *mut crate::leanh::LeanObject,
    mut v_a_2544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idx_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2567_: u8 = 0;
    let mut v_rhs_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_operand_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wExpr_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newWExpr_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_2544_) {
                0 => {
                    v_idx_2545_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc(v_idx_2545_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 2);
                    v___x_2546_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3,
                    );
                    v___x_2547_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2548_ = l_Lean_mkNatLit(v_idx_2545_);
                    v___x_2549_ = l_Lean_mkAppB(v___x_2546_, v___x_2547_, v___x_2548_);
                    return v___x_2549_;
                }
                1 => {
                    v_val_2550_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc(v_val_2550_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 2);
                    v___x_2551_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6,
                    );
                    v___x_2552_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2553_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10,
                    );
                    v___x_2554_ = l_Lean_mkNatLit(v_val_2550_);
                    crate::leanh::lean_inc_ref(v___x_2552_);
                    v___x_2555_ = l_Lean_mkAppB(v___x_2553_, v___x_2552_, v___x_2554_);
                    v___x_2556_ = l_Lean_mkAppB(v___x_2551_, v___x_2552_, v___x_2555_);
                    return v___x_2556_;
                }
                2 => {
                    v_w_2557_ = crate::leanh::lean_ctor_get(v_a_2544_, 0);
                    crate::leanh::lean_inc_n(v_w_2557_, 2);
                    v_start_2558_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc(v_start_2558_);
                    v_expr_2559_ = crate::leanh::lean_ctor_get(v_a_2544_, 3);
                    crate::leanh::lean_inc_ref(v_expr_2559_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 4);
                    v___x_2560_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13,
                    );
                    v___x_2561_ = l_Lean_mkNatLit(v_w_2557_);
                    v___x_2562_ = l_Lean_mkNatLit(v_start_2558_);
                    v___x_2563_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2564_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2557_, v_expr_2559_);
                    v___x_2565_ = l_Lean_mkApp4(
                        v___x_2560_,
                        v___x_2561_,
                        v___x_2562_,
                        v___x_2563_,
                        v___x_2564_,
                    );
                    return v___x_2565_;
                }
                3 => {
                    v_lhs_2566_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc_ref(v_lhs_2566_);
                    v_op_2567_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2544_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v_rhs_2568_ = crate::leanh::lean_ctor_get(v_a_2544_, 2);
                    crate::leanh::lean_inc_ref(v_rhs_2568_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 3);
                    v___x_2569_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16,
                    );
                    crate::leanh::lean_inc_n(v_w_2543_, 2);
                    v___x_2570_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2571_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2543_, v_lhs_2566_);
                    match v_op_2567_ {
                        0 => {
                            v___x_2576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6);
                            v___y_2573_ = v___x_2576_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_2577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9);
                            v___y_2573_ = v___x_2577_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___x_2578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12);
                            v___y_2573_ = v___x_2578_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v___x_2579_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15);
                            v___y_2573_ = v___x_2579_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v___x_2580_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18);
                            v___y_2573_ = v___x_2580_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v___x_2581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21);
                            v___y_2573_ = v___x_2581_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_2582_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24);
                            v___y_2573_ = v___x_2582_;
                            state = 1;
                            continue;
                        }
                    }
                }
                4 => {
                    v_op_2583_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc(v_op_2583_);
                    v_operand_2584_ = crate::leanh::lean_ctor_get(v_a_2544_, 2);
                    crate::leanh::lean_inc_ref(v_operand_2584_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 3);
                    v___x_2585_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19,
                    );
                    crate::leanh::lean_inc(v_w_2543_);
                    v___x_2586_ = l_Lean_mkNatLit(v_w_2543_);
                    match crate::leanh::lean_obj_tag(v_op_2583_) {
                        0 => {
                            v___x_2591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3);
                            v___y_2588_ = v___x_2591_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_n_2592_ = crate::leanh::lean_ctor_get(v_op_2583_, 0);
                            crate::leanh::lean_inc(v_n_2592_);
                            crate::leanh::lean_dec_ref_known(v_op_2583_, 1);
                            v___x_2593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6);
                            v___x_2594_ = l_Lean_mkNatLit(v_n_2592_);
                            v___x_2595_ = l_Lean_Expr_app___override(v___x_2593_, v___x_2594_);
                            v___y_2588_ = v___x_2595_;
                            state = 2;
                            continue;
                        }
                        2 => {
                            v_n_2596_ = crate::leanh::lean_ctor_get(v_op_2583_, 0);
                            crate::leanh::lean_inc(v_n_2596_);
                            crate::leanh::lean_dec_ref_known(v_op_2583_, 1);
                            v___x_2597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9);
                            v___x_2598_ = l_Lean_mkNatLit(v_n_2596_);
                            v___x_2599_ = l_Lean_Expr_app___override(v___x_2597_, v___x_2598_);
                            v___y_2588_ = v___x_2599_;
                            state = 2;
                            continue;
                        }
                        3 => {
                            v_n_2600_ = crate::leanh::lean_ctor_get(v_op_2583_, 0);
                            crate::leanh::lean_inc(v_n_2600_);
                            crate::leanh::lean_dec_ref_known(v_op_2583_, 1);
                            v___x_2601_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12);
                            v___x_2602_ = l_Lean_mkNatLit(v_n_2600_);
                            v___x_2603_ = l_Lean_Expr_app___override(v___x_2601_, v___x_2602_);
                            v___y_2588_ = v___x_2603_;
                            state = 2;
                            continue;
                        }
                        4 => {
                            v___x_2604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15);
                            v___y_2588_ = v___x_2604_;
                            state = 2;
                            continue;
                        }
                        5 => {
                            v___x_2605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18);
                            v___y_2588_ = v___x_2605_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v___x_2606_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21);
                            v___y_2588_ = v___x_2606_;
                            state = 2;
                            continue;
                        }
                    }
                }
                5 => {
                    v_l_2607_ = crate::leanh::lean_ctor_get(v_a_2544_, 0);
                    crate::leanh::lean_inc_n(v_l_2607_, 2);
                    v_r_2608_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc_n(v_r_2608_, 2);
                    v_lhs_2609_ = crate::leanh::lean_ctor_get(v_a_2544_, 3);
                    crate::leanh::lean_inc_ref(v_lhs_2609_);
                    v_rhs_2610_ = crate::leanh::lean_ctor_get(v_a_2544_, 4);
                    crate::leanh::lean_inc_ref(v_rhs_2610_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 5);
                    v_wExpr_2611_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2612_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25,
                    );
                    v___x_2613_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28,
                    );
                    crate::leanh::lean_inc_ref(v_wExpr_2611_);
                    v_proof_2614_ = l_Lean_mkAppB(v___x_2612_, v___x_2613_, v_wExpr_2611_);
                    v___x_2615_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31,
                    );
                    v___x_2616_ = l_Lean_mkNatLit(v_l_2607_);
                    v___x_2617_ = l_Lean_mkNatLit(v_r_2608_);
                    v___x_2618_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_l_2607_, v_lhs_2609_);
                    v___x_2619_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_r_2608_, v_rhs_2610_);
                    v___x_2620_ = l_Lean_mkApp6(
                        v___x_2615_,
                        v___x_2616_,
                        v___x_2617_,
                        v_wExpr_2611_,
                        v___x_2618_,
                        v___x_2619_,
                        v_proof_2614_,
                    );
                    return v___x_2620_;
                }
                6 => {
                    v_w_2621_ = crate::leanh::lean_ctor_get(v_a_2544_, 0);
                    crate::leanh::lean_inc_n(v_w_2621_, 2);
                    v_n_2622_ = crate::leanh::lean_ctor_get(v_a_2544_, 2);
                    crate::leanh::lean_inc(v_n_2622_);
                    v_expr_2623_ = crate::leanh::lean_ctor_get(v_a_2544_, 3);
                    crate::leanh::lean_inc_ref(v_expr_2623_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 4);
                    v_newWExpr_2624_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2625_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25,
                    );
                    v___x_2626_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28,
                    );
                    crate::leanh::lean_inc_ref(v_newWExpr_2624_);
                    v_proof_2627_ = l_Lean_mkAppB(v___x_2625_, v___x_2626_, v_newWExpr_2624_);
                    v___x_2628_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34,
                    );
                    v___x_2629_ = l_Lean_mkNatLit(v_w_2621_);
                    v___x_2630_ = l_Lean_mkNatLit(v_n_2622_);
                    v___x_2631_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2621_, v_expr_2623_);
                    v___x_2632_ = l_Lean_mkApp5(
                        v___x_2628_,
                        v___x_2629_,
                        v_newWExpr_2624_,
                        v___x_2630_,
                        v___x_2631_,
                        v_proof_2627_,
                    );
                    return v___x_2632_;
                }
                7 => {
                    v_n_2633_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc_n(v_n_2633_, 2);
                    v_lhs_2634_ = crate::leanh::lean_ctor_get(v_a_2544_, 2);
                    crate::leanh::lean_inc_ref(v_lhs_2634_);
                    v_rhs_2635_ = crate::leanh::lean_ctor_get(v_a_2544_, 3);
                    crate::leanh::lean_inc_ref(v_rhs_2635_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 4);
                    v___x_2636_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37,
                    );
                    crate::leanh::lean_inc(v_w_2543_);
                    v___x_2637_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2638_ = l_Lean_mkNatLit(v_n_2633_);
                    v___x_2639_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2543_, v_lhs_2634_);
                    v___x_2640_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_2633_, v_rhs_2635_);
                    v___x_2641_ = l_Lean_mkApp4(
                        v___x_2636_,
                        v___x_2637_,
                        v___x_2638_,
                        v___x_2639_,
                        v___x_2640_,
                    );
                    return v___x_2641_;
                }
                8 => {
                    v_n_2642_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc_n(v_n_2642_, 2);
                    v_lhs_2643_ = crate::leanh::lean_ctor_get(v_a_2544_, 2);
                    crate::leanh::lean_inc_ref(v_lhs_2643_);
                    v_rhs_2644_ = crate::leanh::lean_ctor_get(v_a_2544_, 3);
                    crate::leanh::lean_inc_ref(v_rhs_2644_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 4);
                    v___x_2645_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40,
                    );
                    crate::leanh::lean_inc(v_w_2543_);
                    v___x_2646_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2647_ = l_Lean_mkNatLit(v_n_2642_);
                    v___x_2648_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2543_, v_lhs_2643_);
                    v___x_2649_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_2642_, v_rhs_2644_);
                    v___x_2650_ = l_Lean_mkApp4(
                        v___x_2645_,
                        v___x_2646_,
                        v___x_2647_,
                        v___x_2648_,
                        v___x_2649_,
                    );
                    return v___x_2650_;
                }
                _ => {
                    v_n_2651_ = crate::leanh::lean_ctor_get(v_a_2544_, 1);
                    crate::leanh::lean_inc_n(v_n_2651_, 2);
                    v_lhs_2652_ = crate::leanh::lean_ctor_get(v_a_2544_, 2);
                    crate::leanh::lean_inc_ref(v_lhs_2652_);
                    v_rhs_2653_ = crate::leanh::lean_ctor_get(v_a_2544_, 3);
                    crate::leanh::lean_inc_ref(v_rhs_2653_);
                    crate::leanh::lean_dec_ref_known(v_a_2544_, 4);
                    v___x_2654_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43,
                    );
                    crate::leanh::lean_inc(v_w_2543_);
                    v___x_2655_ = l_Lean_mkNatLit(v_w_2543_);
                    v___x_2656_ = l_Lean_mkNatLit(v_n_2651_);
                    v___x_2657_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2543_, v_lhs_2652_);
                    v___x_2658_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_2651_, v_rhs_2653_);
                    v___x_2659_ = l_Lean_mkApp4(
                        v___x_2654_,
                        v___x_2655_,
                        v___x_2656_,
                        v___x_2657_,
                        v___x_2658_,
                    );
                    return v___x_2659_;
                }
            },
            1 => {
                v___x_2574_ =
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2543_, v_rhs_2568_);
                crate::leanh::lean_inc_ref(v___y_2573_);
                v___x_2575_ = l_Lean_mkApp4(
                    v___x_2569_,
                    v___x_2570_,
                    v___x_2571_,
                    v___y_2573_,
                    v___x_2574_,
                );
                return v___x_2575_;
            }
            2 => {
                v___x_2589_ =
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2543_, v_operand_2584_);
                v___x_2590_ = l_Lean_mkApp3(v___x_2585_, v___x_2586_, v___y_2588_, v___x_2589_);
                return v___x_2590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0(
    mut v_w_2660_: *mut crate::leanh::LeanObject,
    mut v_x_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2660_, v_x_2661_);
    return v___x_2662_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = crate::leanh::lean_box(0);
    v___x_2669_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0;
    v___x_2670_ = l_Lean_mkConst(v___x_2669_, v___x_2668_);
    return v___x_2670_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr(
    mut v_w_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_w_2671_);
    v___f_2672_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2672_, 0, v_w_2671_);
    v___x_2673_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1,
    );
    v___x_2674_ = l_Lean_mkNatLit(v_w_2671_);
    v___x_2675_ = l_Lean_Expr_app___override(v___x_2673_, v___x_2674_);
    v___x_2676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2676_, 0, v___f_2672_);
    crate::leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
    return v___x_2676_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2685_ = crate::leanh::lean_box(0);
    v___x_2686_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2;
    v___x_2687_ = l_Lean_mkConst(v___x_2686_, v___x_2685_);
    return v___x_2687_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = crate::leanh::lean_box(0);
    v___x_2696_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5;
    v___x_2697_ = l_Lean_mkConst(v___x_2696_, v___x_2695_);
    return v___x_2697_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(
    mut v_x_2698_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_2698_ == 0 {
        let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2699_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once
            ),
            _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3,
        );
        return v___x_2699_;
    } else {
        let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2700_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once
            ),
            _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6,
        );
        return v___x_2700_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___boxed(
    mut v_x_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2702_: u8 = 0;
    let mut v_res_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2702_ = (crate::leanh::lean_unbox(v_x_2701_) as u8);
    v_res_2703_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(v_x_boxed_2702_);
    return v_res_2703_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = crate::leanh::lean_box(0);
    v___x_2711_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1;
    v___x_2712_ = l_Lean_mkConst(v___x_2711_, v___x_2710_);
    return v___x_2712_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2,
    );
    v___f_2714_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0;
    v___x_2715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2715_, 0, v___f_2714_);
    crate::leanh::lean_ctor_set(v___x_2715_, 1, v___x_2713_);
    return v___x_2715_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3,
    );
    return v___x_2716_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2724_ = crate::leanh::lean_box(0);
    v___x_2725_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1;
    v___x_2726_ = l_Lean_mkConst(v___x_2725_, v___x_2724_);
    return v___x_2726_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = crate::leanh::lean_box(0);
    v___x_2734_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3;
    v___x_2735_ = l_Lean_mkConst(v___x_2734_, v___x_2733_);
    return v___x_2735_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2743_ = crate::leanh::lean_box(0);
    v___x_2744_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6;
    v___x_2745_ = l_Lean_mkConst(v___x_2744_, v___x_2743_);
    return v___x_2745_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = crate::leanh::lean_box(0);
    v___x_2753_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8;
    v___x_2754_ = l_Lean_mkConst(v___x_2753_, v___x_2752_);
    return v___x_2754_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(
    mut v_x_2755_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2755_ {
        0 => {
            let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2756_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2,
            );
            return v___x_2756_;
        }
        1 => {
            let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2757_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4,
            );
            return v___x_2757_;
        }
        2 => {
            let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2758_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7,
            );
            return v___x_2758_;
        }
        _ => {
            let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2759_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once
                ),
                _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9,
            );
            return v___x_2759_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___boxed(
    mut v_x_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2761_: u8 = 0;
    let mut v_res_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2761_ = (crate::leanh::lean_unbox(v_x_2760_) as u8);
    v_res_2762_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(v_x_boxed_2761_);
    return v_res_2762_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2769_ = crate::leanh::lean_box(0);
    v___x_2770_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1;
    v___x_2771_ = l_Lean_mkConst(v___x_2770_, v___x_2769_);
    return v___x_2771_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2,
    );
    v___f_2773_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0;
    v___x_2774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2774_, 0, v___f_2773_);
    crate::leanh::lean_ctor_set(v___x_2774_, 1, v___x_2772_);
    return v___x_2774_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate() -> *mut crate::leanh::LeanObject {
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3,
    );
    return v___x_2775_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2783_ = crate::leanh::lean_box(0);
    v___x_2784_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1;
    v___x_2785_ = l_Lean_mkConst(v___x_2784_, v___x_2783_);
    return v___x_2785_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2793_ = crate::leanh::lean_box(0);
    v___x_2794_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4;
    v___x_2795_ = l_Lean_mkConst(v___x_2794_, v___x_2793_);
    return v___x_2795_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go(
    mut v_a_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2799_: u8 = 0;
    let mut v_rhs_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2796_) == 0 {
                    v_w_2797_ = crate::leanh::lean_ctor_get(v_a_2796_, 0);
                    crate::leanh::lean_inc_n(v_w_2797_, 3);
                    v_lhs_2798_ = crate::leanh::lean_ctor_get(v_a_2796_, 1);
                    crate::leanh::lean_inc_ref(v_lhs_2798_);
                    v_op_2799_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2796_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_rhs_2800_ = crate::leanh::lean_ctor_get(v_a_2796_, 2);
                    crate::leanh::lean_inc_ref(v_rhs_2800_);
                    crate::leanh::lean_dec_ref_known(v_a_2796_, 3);
                    v___x_2801_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2,
                    );
                    v___x_2802_ = l_Lean_mkNatLit(v_w_2797_);
                    v___x_2803_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2797_, v_lhs_2798_);
                    if v_op_2799_ == 0 {
                        v___x_2808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3);
                        v___y_2805_ = v___x_2808_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6);
                        v___y_2805_ = v___x_2809_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_w_2810_ = crate::leanh::lean_ctor_get(v_a_2796_, 0);
                    crate::leanh::lean_inc_n(v_w_2810_, 2);
                    v_expr_2811_ = crate::leanh::lean_ctor_get(v_a_2796_, 1);
                    crate::leanh::lean_inc_ref(v_expr_2811_);
                    v_idx_2812_ = crate::leanh::lean_ctor_get(v_a_2796_, 2);
                    crate::leanh::lean_inc(v_idx_2812_);
                    crate::leanh::lean_dec_ref_known(v_a_2796_, 3);
                    v___x_2813_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5,
                    );
                    v___x_2814_ = l_Lean_mkNatLit(v_w_2810_);
                    v___x_2815_ =
                        l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2810_, v_expr_2811_);
                    v___x_2816_ = l_Lean_mkNatLit(v_idx_2812_);
                    v___x_2817_ = l_Lean_mkApp3(v___x_2813_, v___x_2814_, v___x_2815_, v___x_2816_);
                    return v___x_2817_;
                }
            }
            1 => {
                v___x_2806_ =
                    l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_2797_, v_rhs_2800_);
                crate::leanh::lean_inc_ref(v___y_2805_);
                v___x_2807_ = l_Lean_mkApp4(
                    v___x_2801_,
                    v___x_2802_,
                    v___x_2803_,
                    v___y_2805_,
                    v___x_2806_,
                );
                return v___x_2807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = crate::leanh::lean_box(0);
    v___x_2825_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1;
    v___x_2826_ = l_Lean_mkConst(v___x_2825_, v___x_2824_);
    return v___x_2826_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2,
    );
    v___f_2828_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0;
    v___x_2829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2829_, 0, v___f_2828_);
    crate::leanh::lean_ctor_set(v___x_2829_, 1, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3,
    );
    return v___x_2830_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2839_ = crate::leanh::lean_box(0);
    v___x_2840_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2;
    v___x_2841_ = l_Lean_mkConst(v___x_2840_, v___x_2839_);
    return v___x_2841_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = crate::leanh::lean_box(0);
    v___x_2849_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4;
    v___x_2850_ = l_Lean_mkConst(v___x_2849_, v___x_2848_);
    return v___x_2850_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2856_ = crate::leanh::lean_box(0);
    v___x_2857_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8;
    v___x_2858_ = l_Lean_mkConst(v___x_2857_, v___x_2856_);
    return v___x_2858_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = crate::leanh::lean_box(0);
    v___x_2864_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11;
    v___x_2865_ = l_Lean_mkConst(v___x_2864_, v___x_2863_);
    return v___x_2865_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = crate::leanh::lean_box(0);
    v___x_2873_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13;
    v___x_2874_ = l_Lean_mkConst(v___x_2873_, v___x_2872_);
    return v___x_2874_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = crate::leanh::lean_box(0);
    v___x_2883_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16;
    v___x_2884_ = l_Lean_mkConst(v___x_2883_, v___x_2882_);
    return v___x_2884_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2892_ = crate::leanh::lean_box(0);
    v___x_2893_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19;
    v___x_2894_ = l_Lean_mkConst(v___x_2893_, v___x_2892_);
    return v___x_2894_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
    mut v_inst_2895_: *mut crate::leanh::LeanObject,
    mut v_a_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toExpr_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2903_: u8 = 0;
    let mut v_toTypeExpr_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: u8 = 0;
    let mut v_a_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_2896_) {
                0 => {
                    v_a_2897_ = crate::leanh::lean_ctor_get(v_a_2896_, 0);
                    crate::leanh::lean_inc(v_a_2897_);
                    crate::leanh::lean_dec_ref_known(v_a_2896_, 1);
                    v_toExpr_2898_ = crate::leanh::lean_ctor_get(v_inst_2895_, 0);
                    crate::leanh::lean_inc_ref(v_toExpr_2898_);
                    v_toTypeExpr_2899_ = crate::leanh::lean_ctor_get(v_inst_2895_, 1);
                    crate::leanh::lean_inc_ref(v_toTypeExpr_2899_);
                    crate::leanh::lean_dec_ref(v_inst_2895_);
                    v___x_2900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3);
                    v___x_2901_ = crate::leanh::lean_apply_1(v_toExpr_2898_, v_a_2897_);
                    v___x_2902_ = l_Lean_mkAppB(v___x_2900_, v_toTypeExpr_2899_, v___x_2901_);
                    return v___x_2902_;
                }
                1 => {
                    v_a_2903_ = crate::leanh::lean_ctor_get_uint8(v_a_2896_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_a_2896_, 0);
                    v_toTypeExpr_2904_ = crate::leanh::lean_ctor_get(v_inst_2895_, 1);
                    crate::leanh::lean_inc_ref(v_toTypeExpr_2904_);
                    crate::leanh::lean_dec_ref(v_inst_2895_);
                    v___x_2905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5);
                    if v_a_2903_ == 0 {
                        v___x_2906_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9);
                        v___x_2907_ = l_Lean_mkAppB(v___x_2905_, v_toTypeExpr_2904_, v___x_2906_);
                        return v___x_2907_;
                    } else {
                        v___x_2908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12);
                        v___x_2909_ = l_Lean_mkAppB(v___x_2905_, v_toTypeExpr_2904_, v___x_2908_);
                        return v___x_2909_;
                    }
                }
                2 => {
                    v_a_2910_ = crate::leanh::lean_ctor_get(v_a_2896_, 0);
                    crate::leanh::lean_inc_ref(v_a_2910_);
                    crate::leanh::lean_dec_ref_known(v_a_2896_, 1);
                    v_toTypeExpr_2911_ = crate::leanh::lean_ctor_get(v_inst_2895_, 1);
                    crate::leanh::lean_inc_ref(v_toTypeExpr_2911_);
                    v___x_2912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14);
                    v___x_2913_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
                        v_inst_2895_,
                        v_a_2910_,
                    );
                    v___x_2914_ = l_Lean_mkAppB(v___x_2912_, v_toTypeExpr_2911_, v___x_2913_);
                    return v___x_2914_;
                }
                3 => {
                    v_a_2915_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2896_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_a_2916_ = crate::leanh::lean_ctor_get(v_a_2896_, 0);
                    crate::leanh::lean_inc_ref(v_a_2916_);
                    v_a_2917_ = crate::leanh::lean_ctor_get(v_a_2896_, 1);
                    crate::leanh::lean_inc_ref(v_a_2917_);
                    crate::leanh::lean_dec_ref_known(v_a_2896_, 2);
                    v_toTypeExpr_2918_ = crate::leanh::lean_ctor_get(v_inst_2895_, 1);
                    crate::leanh::lean_inc_ref(v_toTypeExpr_2918_);
                    v___x_2919_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17);
                    match v_a_2915_ {
                        0 => {
                            v___x_2925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2);
                            v___y_2921_ = v___x_2925_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_2926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4);
                            v___y_2921_ = v___x_2926_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___x_2927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7);
                            v___y_2921_ = v___x_2927_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_2928_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9);
                            v___y_2921_ = v___x_2928_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    v_a_2929_ = crate::leanh::lean_ctor_get(v_a_2896_, 0);
                    crate::leanh::lean_inc_ref(v_a_2929_);
                    v_a_2930_ = crate::leanh::lean_ctor_get(v_a_2896_, 1);
                    crate::leanh::lean_inc_ref(v_a_2930_);
                    v_a_2931_ = crate::leanh::lean_ctor_get(v_a_2896_, 2);
                    crate::leanh::lean_inc_ref(v_a_2931_);
                    crate::leanh::lean_dec_ref_known(v_a_2896_, 3);
                    v_toTypeExpr_2932_ = crate::leanh::lean_ctor_get(v_inst_2895_, 1);
                    crate::leanh::lean_inc_ref(v_toTypeExpr_2932_);
                    v___x_2933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20_once), _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20);
                    crate::leanh::lean_inc_ref_n(v_inst_2895_, 2);
                    v___x_2934_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
                        v_inst_2895_,
                        v_a_2929_,
                    );
                    v___x_2935_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
                        v_inst_2895_,
                        v_a_2930_,
                    );
                    v___x_2936_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
                        v_inst_2895_,
                        v_a_2931_,
                    );
                    v___x_2937_ = l_Lean_mkApp4(
                        v___x_2933_,
                        v_toTypeExpr_2932_,
                        v___x_2934_,
                        v___x_2935_,
                        v___x_2936_,
                    );
                    return v___x_2937_;
                }
            },
            1 => {
                crate::leanh::lean_inc_ref(v_inst_2895_);
                v___x_2922_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
                    v_inst_2895_,
                    v_a_2916_,
                );
                v___x_2923_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(
                    v_inst_2895_,
                    v_a_2917_,
                );
                crate::leanh::lean_inc_ref(v___y_2921_);
                v___x_2924_ = l_Lean_mkApp4(
                    v___x_2919_,
                    v_toTypeExpr_2918_,
                    v___y_2921_,
                    v___x_2922_,
                    v___x_2923_,
                );
                return v___x_2924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go(
    mut v_00_u03b1_2938_: *mut crate::leanh::LeanObject,
    mut v_inst_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ =
        l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_2939_, v_a_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0(
    mut v_inst_2942_: *mut crate::leanh::LeanObject,
    mut v_x_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2944_ =
        l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_2942_, v_x_2943_);
    return v___x_2944_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2950_ = crate::leanh::lean_box(0);
    v___x_2951_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0;
    v___x_2952_ = l_Lean_mkConst(v___x_2951_, v___x_2950_);
    return v___x_2952_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(
    mut v_inst_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTypeExpr_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toTypeExpr_2954_ = crate::leanh::lean_ctor_get(v_inst_2953_, 1);
    crate::leanh::lean_inc_ref(v_toTypeExpr_2954_);
    v___f_2955_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2955_, 0, v_inst_2953_);
    v___x_2956_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1,
    );
    v___x_2957_ = l_Lean_Expr_app___override(v___x_2956_, v_toTypeExpr_2954_);
    v___x_2958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2958_, 0, v___f_2955_);
    crate::leanh::lean_ctor_set(v___x_2958_, 1, v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr(
    mut v_00_u03b1_2959_: *mut crate::leanh::LeanObject,
    mut v_inst_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(v_inst_2960_);
    return v___x_2961_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(
    mut v_a_2962_: *mut crate::leanh::LeanObject,
    mut v_x_2963_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2964_: u8 = 0;
    let mut v_key_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2963_) == 0 {
                    v___x_2964_ = 0;
                    return v___x_2964_;
                } else {
                    v_key_2965_ = crate::leanh::lean_ctor_get(v_x_2963_, 0);
                    v_tail_2966_ = crate::leanh::lean_ctor_get(v_x_2963_, 2);
                    v___x_2967_ = lean_expr_eqv(v_key_2965_, v_a_2962_);
                    if v___x_2967_ == 0 {
                        v_x_2963_ = v_tail_2966_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2967_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_x_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: u8 = 0;
    let mut v_r_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_2969_, v_x_2970_);
    crate::leanh::lean_dec(v_x_2970_);
    crate::leanh::lean_dec_ref(v_a_2969_);
    v_r_2972_ = crate::leanh::lean_box((v_res_2971_) as usize);
    return v_r_2972_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_2973_: *mut crate::leanh::LeanObject,
    mut v_x_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u64 = 0;
    let mut v___x_2983_: u64 = 0;
    let mut v___x_2984_: u64 = 0;
    let mut v_fold_2985_: u64 = 0;
    let mut v___x_2986_: u64 = 0;
    let mut v___x_2987_: u64 = 0;
    let mut v___x_2988_: u64 = 0;
    let mut v___x_2989_: usize = 0;
    let mut v___x_2990_: usize = 0;
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut v___x_2993_: usize = 0;
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2974_) == 0 {
                    return v_x_2973_;
                } else {
                    v_key_2975_ = crate::leanh::lean_ctor_get(v_x_2974_, 0);
                    v_value_2976_ = crate::leanh::lean_ctor_get(v_x_2974_, 1);
                    v_tail_2977_ = crate::leanh::lean_ctor_get(v_x_2974_, 2);
                    v_isSharedCheck_3000_ = (!crate::leanh::lean_is_exclusive(v_x_2974_)) as u8;
                    if v_isSharedCheck_3000_ == 0 {
                        v___x_2979_ = v_x_2974_;
                        v_isShared_2980_ = v_isSharedCheck_3000_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2977_);
                        crate::leanh::lean_inc(v_value_2976_);
                        crate::leanh::lean_inc(v_key_2975_);
                        crate::leanh::lean_dec(v_x_2974_);
                        v___x_2979_ = crate::leanh::lean_box(0);
                        v_isShared_2980_ = v_isSharedCheck_3000_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2981_ = lean_array_get_size(v_x_2973_);
                v___x_2982_ = l_Lean_Expr_hash(v_key_2975_);
                v___x_2983_ = 32u64;
                v___x_2984_ = lean_uint64_shift_right(v___x_2982_, v___x_2983_);
                v_fold_2985_ = lean_uint64_xor(v___x_2982_, v___x_2984_);
                v___x_2986_ = 16u64;
                v___x_2987_ = lean_uint64_shift_right(v_fold_2985_, v___x_2986_);
                v___x_2988_ = lean_uint64_xor(v_fold_2985_, v___x_2987_);
                v___x_2989_ = lean_uint64_to_usize(v___x_2988_);
                v___x_2990_ = lean_usize_of_nat(v___x_2981_);
                v___x_2991_ = 1usize;
                v___x_2992_ = lean_usize_sub(v___x_2990_, v___x_2991_);
                v___x_2993_ = lean_usize_land(v___x_2989_, v___x_2992_);
                v___x_2994_ = lean_array_uget_borrowed(v_x_2973_, v___x_2993_);
                crate::leanh::lean_inc(v___x_2994_);
                if v_isShared_2980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2979_, 2, v___x_2994_);
                    v___x_2996_ = v___x_2979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2999_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_key_2975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_value_2976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 2, v___x_2994_);
                    v___x_2996_ = v_reuseFailAlloc_2999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2997_ = lean_array_uset(v_x_2973_, v___x_2993_, v___x_2996_);
                v_x_2973_ = v___x_2997_;
                v_x_2974_ = v_tail_2977_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(
    mut v_i_3001_: *mut crate::leanh::LeanObject,
    mut v_source_3002_: *mut crate::leanh::LeanObject,
    mut v_target_3003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: u8 = 0;
    let mut v_es_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3004_ = lean_array_get_size(v_source_3002_);
                v___x_3005_ = lean_nat_dec_lt(v_i_3001_, v___x_3004_);
                if v___x_3005_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3002_);
                    crate::leanh::lean_dec(v_i_3001_);
                    return v_target_3003_;
                } else {
                    v_es_3006_ = lean_array_fget(v_source_3002_, v_i_3001_);
                    v___x_3007_ = crate::leanh::lean_box(0);
                    v_source_3008_ = lean_array_fset(v_source_3002_, v_i_3001_, v___x_3007_);
                    v_target_3009_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_target_3003_, v_es_3006_);
                    v___x_3010_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3011_ = lean_nat_add(v_i_3001_, v___x_3010_);
                    crate::leanh::lean_dec(v_i_3001_);
                    v_i_3001_ = v___x_3011_;
                    v_source_3002_ = v_source_3008_;
                    v_target_3003_ = v_target_3009_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(
    mut v_data_3013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3014_ = lean_array_get_size(v_data_3013_);
    v___x_3015_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3016_ = lean_nat_mul(v___x_3014_, v___x_3015_);
    v___x_3017_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3018_ = crate::leanh::lean_box(0);
    v___x_3019_ = lean_mk_array(v_nbuckets_3016_, v___x_3018_);
    v___x_3020_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v___x_3017_, v_data_3013_, v___x_3019_);
    return v___x_3020_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_b_3022_: *mut crate::leanh::LeanObject,
    mut v_x_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3023_) == 0 {
                    crate::leanh::lean_dec(v_b_3022_);
                    crate::leanh::lean_dec_ref(v_a_3021_);
                    return v_x_3023_;
                } else {
                    v_key_3024_ = crate::leanh::lean_ctor_get(v_x_3023_, 0);
                    v_value_3025_ = crate::leanh::lean_ctor_get(v_x_3023_, 1);
                    v_tail_3026_ = crate::leanh::lean_ctor_get(v_x_3023_, 2);
                    v_isSharedCheck_3038_ = (!crate::leanh::lean_is_exclusive(v_x_3023_)) as u8;
                    if v_isSharedCheck_3038_ == 0 {
                        v___x_3028_ = v_x_3023_;
                        v_isShared_3029_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3026_);
                        crate::leanh::lean_inc(v_value_3025_);
                        crate::leanh::lean_inc(v_key_3024_);
                        crate::leanh::lean_dec(v_x_3023_);
                        v___x_3028_ = crate::leanh::lean_box(0);
                        v_isShared_3029_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3030_ = lean_expr_eqv(v_key_3024_, v_a_3021_);
                if v___x_3030_ == 0 {
                    v___x_3031_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_3021_, v_b_3022_, v_tail_3026_);
                    if v_isShared_3029_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3028_, 2, v___x_3031_);
                        v___x_3033_ = v___x_3028_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_key_3024_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_value_3025_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 2, v___x_3031_);
                        v___x_3033_ = v_reuseFailAlloc_3034_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3025_);
                    crate::leanh::lean_dec(v_key_3024_);
                    if v_isShared_3029_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3028_, 1, v_b_3022_);
                        crate::leanh::lean_ctor_set(v___x_3028_, 0, v_a_3021_);
                        v___x_3036_ = v___x_3028_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3037_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3021_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_b_3022_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_tail_3026_);
                        v___x_3036_ = v_reuseFailAlloc_3037_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3033_;
            }
            3 => {
                return v___x_3036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(
    mut v_m_3039_: *mut crate::leanh::LeanObject,
    mut v_a_3040_: *mut crate::leanh::LeanObject,
    mut v_b_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: u64 = 0;
    let mut v___x_3049_: u64 = 0;
    let mut v___x_3050_: u64 = 0;
    let mut v_fold_3051_: u64 = 0;
    let mut v___x_3052_: u64 = 0;
    let mut v___x_3053_: u64 = 0;
    let mut v___x_3054_: u64 = 0;
    let mut v___x_3055_: usize = 0;
    let mut v___x_3056_: usize = 0;
    let mut v___x_3057_: usize = 0;
    let mut v___x_3058_: usize = 0;
    let mut v___x_3059_: usize = 0;
    let mut v_bkt_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    let mut v_val_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3042_ = crate::leanh::lean_ctor_get(v_m_3039_, 0);
                v_buckets_3043_ = crate::leanh::lean_ctor_get(v_m_3039_, 1);
                v_isSharedCheck_3086_ = (!crate::leanh::lean_is_exclusive(v_m_3039_)) as u8;
                if v_isSharedCheck_3086_ == 0 {
                    v___x_3045_ = v_m_3039_;
                    v_isShared_3046_ = v_isSharedCheck_3086_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3043_);
                    crate::leanh::lean_inc(v_size_3042_);
                    crate::leanh::lean_dec(v_m_3039_);
                    v___x_3045_ = crate::leanh::lean_box(0);
                    v_isShared_3046_ = v_isSharedCheck_3086_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3047_ = lean_array_get_size(v_buckets_3043_);
                v___x_3048_ = l_Lean_Expr_hash(v_a_3040_);
                v___x_3049_ = 32u64;
                v___x_3050_ = lean_uint64_shift_right(v___x_3048_, v___x_3049_);
                v_fold_3051_ = lean_uint64_xor(v___x_3048_, v___x_3050_);
                v___x_3052_ = 16u64;
                v___x_3053_ = lean_uint64_shift_right(v_fold_3051_, v___x_3052_);
                v___x_3054_ = lean_uint64_xor(v_fold_3051_, v___x_3053_);
                v___x_3055_ = lean_uint64_to_usize(v___x_3054_);
                v___x_3056_ = lean_usize_of_nat(v___x_3047_);
                v___x_3057_ = 1usize;
                v___x_3058_ = lean_usize_sub(v___x_3056_, v___x_3057_);
                v___x_3059_ = lean_usize_land(v___x_3055_, v___x_3058_);
                v_bkt_3060_ = lean_array_uget_borrowed(v_buckets_3043_, v___x_3059_);
                v___x_3061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_3040_, v_bkt_3060_);
                if v___x_3061_ == 0 {
                    v___x_3062_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3063_ = lean_nat_add(v_size_3042_, v___x_3062_);
                    crate::leanh::lean_dec(v_size_3042_);
                    crate::leanh::lean_inc(v_bkt_3060_);
                    v___x_3064_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3064_, 0, v_a_3040_);
                    crate::leanh::lean_ctor_set(v___x_3064_, 1, v_b_3041_);
                    crate::leanh::lean_ctor_set(v___x_3064_, 2, v_bkt_3060_);
                    v_buckets_x27_3065_ =
                        lean_array_uset(v_buckets_3043_, v___x_3059_, v___x_3064_);
                    v___x_3066_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3067_ = lean_nat_mul(v_size_x27_3063_, v___x_3066_);
                    v___x_3068_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3069_ = lean_nat_div(v___x_3067_, v___x_3068_);
                    crate::leanh::lean_dec(v___x_3067_);
                    v___x_3070_ = lean_array_get_size(v_buckets_x27_3065_);
                    v___x_3071_ = lean_nat_dec_le(v___x_3069_, v___x_3070_);
                    crate::leanh::lean_dec(v___x_3069_);
                    if v___x_3071_ == 0 {
                        v_val_3072_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_buckets_x27_3065_);
                        if v_isShared_3046_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3045_, 1, v_val_3072_);
                            crate::leanh::lean_ctor_set(v___x_3045_, 0, v_size_x27_3063_);
                            v___x_3074_ = v___x_3045_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3075_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3075_,
                                0,
                                v_size_x27_3063_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_val_3072_);
                            v___x_3074_ = v_reuseFailAlloc_3075_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3046_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3045_, 1, v_buckets_x27_3065_);
                            crate::leanh::lean_ctor_set(v___x_3045_, 0, v_size_x27_3063_);
                            v___x_3077_ = v___x_3045_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3078_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3078_,
                                0,
                                v_size_x27_3063_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3078_,
                                1,
                                v_buckets_x27_3065_,
                            );
                            v___x_3077_ = v_reuseFailAlloc_3078_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3060_);
                    v___x_3079_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3080_ =
                        lean_array_uset(v_buckets_3043_, v___x_3059_, v___x_3079_);
                    v___x_3081_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_3040_, v_b_3041_, v_bkt_3060_);
                    v___x_3082_ = lean_array_uset(v_buckets_x27_3080_, v___x_3059_, v___x_3081_);
                    if v_isShared_3046_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3045_, 1, v___x_3082_);
                        v___x_3084_ = v___x_3045_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3085_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_size_3042_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3082_);
                        v___x_3084_ = v_reuseFailAlloc_3085_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3074_;
            }
            3 => {
                return v___x_3077_;
            }
            4 => {
                return v___x_3084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(
    mut v_a_3087_: *mut crate::leanh::LeanObject,
    mut v_x_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3088_) == 0 {
                    v___x_3089_ = crate::leanh::lean_box(0);
                    return v___x_3089_;
                } else {
                    v_key_3090_ = crate::leanh::lean_ctor_get(v_x_3088_, 0);
                    v_value_3091_ = crate::leanh::lean_ctor_get(v_x_3088_, 1);
                    v_tail_3092_ = crate::leanh::lean_ctor_get(v_x_3088_, 2);
                    v___x_3093_ = lean_expr_eqv(v_key_3090_, v_a_3087_);
                    if v___x_3093_ == 0 {
                        v_x_3088_ = v_tail_3092_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3091_);
                        v___x_3095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3095_, 0, v_value_3091_);
                        return v___x_3095_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(
    mut v_a_3096_: *mut crate::leanh::LeanObject,
    mut v_x_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_3096_, v_x_3097_);
    crate::leanh::lean_dec(v_x_3097_);
    crate::leanh::lean_dec_ref(v_a_3096_);
    return v_res_3098_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(
    mut v_m_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u64 = 0;
    let mut v___x_3104_: u64 = 0;
    let mut v___x_3105_: u64 = 0;
    let mut v_fold_3106_: u64 = 0;
    let mut v___x_3107_: u64 = 0;
    let mut v___x_3108_: u64 = 0;
    let mut v___x_3109_: u64 = 0;
    let mut v___x_3110_: usize = 0;
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: usize = 0;
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3101_ = crate::leanh::lean_ctor_get(v_m_3099_, 1);
    v___x_3102_ = lean_array_get_size(v_buckets_3101_);
    v___x_3103_ = l_Lean_Expr_hash(v_a_3100_);
    v___x_3104_ = 32u64;
    v___x_3105_ = lean_uint64_shift_right(v___x_3103_, v___x_3104_);
    v_fold_3106_ = lean_uint64_xor(v___x_3103_, v___x_3105_);
    v___x_3107_ = 16u64;
    v___x_3108_ = lean_uint64_shift_right(v_fold_3106_, v___x_3107_);
    v___x_3109_ = lean_uint64_xor(v_fold_3106_, v___x_3108_);
    v___x_3110_ = lean_uint64_to_usize(v___x_3109_);
    v___x_3111_ = lean_usize_of_nat(v___x_3102_);
    v___x_3112_ = 1usize;
    v___x_3113_ = lean_usize_sub(v___x_3111_, v___x_3112_);
    v___x_3114_ = lean_usize_land(v___x_3110_, v___x_3113_);
    v___x_3115_ = lean_array_uget_borrowed(v_buckets_3101_, v___x_3114_);
    v___x_3116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_3100_, v___x_3115_);
    return v___x_3116_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(
    mut v_m_3117_: *mut crate::leanh::LeanObject,
    mut v_a_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_3117_, v_a_3118_);
    crate::leanh::lean_dec_ref(v_a_3118_);
    crate::leanh::lean_dec_ref(v_m_3117_);
    return v_res_3119_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
    mut v_reified_3120_: *mut crate::leanh::LeanObject,
    mut v_a_3121_: *mut crate::leanh::LeanObject,
    mut v_a_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_originalExpr_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtAtoms_x27_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atoms_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomsAssignmentCache_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_isSharedCheck_3153_: u8 = 0;
    let mut v_val_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3127_ = lean_st_ref_get(v_a_3121_);
                v_evalsAtCache_3128_ = crate::leanh::lean_ctor_get(v___x_3127_, 2);
                crate::leanh::lean_inc_ref(v_evalsAtCache_3128_);
                crate::leanh::lean_dec(v___x_3127_);
                v_originalExpr_3129_ = crate::leanh::lean_ctor_get(v_reified_3120_, 2);
                crate::leanh::lean_inc_ref(v_originalExpr_3129_);
                v_evalsAtAtoms_x27_3130_ = crate::leanh::lean_ctor_get(v_reified_3120_, 3);
                crate::leanh::lean_inc_ref(v_evalsAtAtoms_x27_3130_);
                crate::leanh::lean_dec_ref(v_reified_3120_);
                v___x_3131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_3128_, v_originalExpr_3129_);
                crate::leanh::lean_dec_ref(v_evalsAtCache_3128_);
                if crate::leanh::lean_obj_tag(v___x_3131_) == 0 {
                    crate::leanh::lean_inc(v_a_3125_);
                    crate::leanh::lean_inc_ref(v_a_3124_);
                    crate::leanh::lean_inc(v_a_3123_);
                    crate::leanh::lean_inc_ref(v_a_3122_);
                    crate::leanh::lean_inc(v_a_3121_);
                    v___x_3132_ = crate::leanh::lean_apply_6(
                        v_evalsAtAtoms_x27_3130_,
                        v_a_3121_,
                        v_a_3122_,
                        v_a_3123_,
                        v_a_3124_,
                        v_a_3125_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3132_) == 0 {
                        v_a_3133_ = crate::leanh::lean_ctor_get(v___x_3132_, 0);
                        v_isSharedCheck_3153_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3132_)) as u8;
                        if v_isSharedCheck_3153_ == 0 {
                            v___x_3135_ = v___x_3132_;
                            v_isShared_3136_ = v_isSharedCheck_3153_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3133_);
                            crate::leanh::lean_dec(v___x_3132_);
                            v___x_3135_ = crate::leanh::lean_box(0);
                            v_isShared_3136_ = v_isSharedCheck_3153_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_originalExpr_3129_);
                        return v___x_3132_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_evalsAtAtoms_x27_3130_);
                    crate::leanh::lean_dec_ref(v_originalExpr_3129_);
                    v_val_3154_ = crate::leanh::lean_ctor_get(v___x_3131_, 0);
                    v_isSharedCheck_3161_ = (!crate::leanh::lean_is_exclusive(v___x_3131_)) as u8;
                    if v_isSharedCheck_3161_ == 0 {
                        v___x_3156_ = v___x_3131_;
                        v_isShared_3157_ = v_isSharedCheck_3161_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3154_);
                        crate::leanh::lean_dec(v___x_3131_);
                        v___x_3156_ = crate::leanh::lean_box(0);
                        v_isShared_3157_ = v_isSharedCheck_3161_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3137_ = lean_st_ref_take(v_a_3121_);
                v_atoms_3138_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                v_atomsAssignmentCache_3139_ = crate::leanh::lean_ctor_get(v___x_3137_, 1);
                v_evalsAtCache_3140_ = crate::leanh::lean_ctor_get(v___x_3137_, 2);
                v_isSharedCheck_3152_ = (!crate::leanh::lean_is_exclusive(v___x_3137_)) as u8;
                if v_isSharedCheck_3152_ == 0 {
                    v___x_3142_ = v___x_3137_;
                    v_isShared_3143_ = v_isSharedCheck_3152_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_evalsAtCache_3140_);
                    crate::leanh::lean_inc(v_atomsAssignmentCache_3139_);
                    crate::leanh::lean_inc(v_atoms_3138_);
                    crate::leanh::lean_dec(v___x_3137_);
                    v___x_3142_ = crate::leanh::lean_box(0);
                    v_isShared_3143_ = v_isSharedCheck_3152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_3133_);
                v___x_3144_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_3140_, v_originalExpr_3129_, v_a_3133_);
                if v_isShared_3143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3142_, 2, v___x_3144_);
                    v___x_3146_ = v___x_3142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_atoms_3138_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3151_,
                        1,
                        v_atomsAssignmentCache_3139_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 2, v___x_3144_);
                    v___x_3146_ = v_reuseFailAlloc_3151_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3147_ = lean_st_ref_set(v_a_3121_, v___x_3146_);
                if v_isShared_3136_ == 0 {
                    v___x_3149_ = v___x_3135_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3133_);
                    v___x_3149_ = v_reuseFailAlloc_3150_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3149_;
            }
            5 => {
                if v_isShared_3157_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3156_, 0);
                    v___x_3159_ = v___x_3156_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_val_3154_);
                    v___x_3159_ = v_reuseFailAlloc_3160_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms___boxed(
    mut v_reified_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3169_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
        v_reified_3162_,
        v_a_3163_,
        v_a_3164_,
        v_a_3165_,
        v_a_3166_,
        v_a_3167_,
    );
    crate::leanh::lean_dec(v_a_3167_);
    crate::leanh::lean_dec_ref(v_a_3166_);
    crate::leanh::lean_dec(v_a_3165_);
    crate::leanh::lean_dec_ref(v_a_3164_);
    crate::leanh::lean_dec(v_a_3163_);
    return v_res_3169_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(
    mut v_00_u03b2_3170_: *mut crate::leanh::LeanObject,
    mut v_m_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_3171_, v_a_3172_);
    return v___x_3173_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(
    mut v_00_u03b2_3174_: *mut crate::leanh::LeanObject,
    mut v_m_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(v_00_u03b2_3174_, v_m_3175_, v_a_3176_);
    crate::leanh::lean_dec_ref(v_a_3176_);
    crate::leanh::lean_dec_ref(v_m_3175_);
    return v_res_3177_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(
    mut v_00_u03b2_3178_: *mut crate::leanh::LeanObject,
    mut v_m_3179_: *mut crate::leanh::LeanObject,
    mut v_a_3180_: *mut crate::leanh::LeanObject,
    mut v_b_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_3179_, v_a_3180_, v_b_3181_);
    return v___x_3182_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(
    mut v_00_u03b2_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_x_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3186_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_3184_, v_x_3185_);
    return v___x_3186_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(
    mut v_00_u03b2_3187_: *mut crate::leanh::LeanObject,
    mut v_a_3188_: *mut crate::leanh::LeanObject,
    mut v_x_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3190_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(v_00_u03b2_3187_, v_a_3188_, v_x_3189_);
    crate::leanh::lean_dec(v_x_3189_);
    crate::leanh::lean_dec_ref(v_a_3188_);
    return v_res_3190_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(
    mut v_00_u03b2_3191_: *mut crate::leanh::LeanObject,
    mut v_a_3192_: *mut crate::leanh::LeanObject,
    mut v_x_3193_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3194_: u8 = 0;
    v___x_3194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_3192_, v_x_3193_);
    return v___x_3194_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(
    mut v_00_u03b2_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
    mut v_x_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3198_: u8 = 0;
    let mut v_r_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(v_00_u03b2_3195_, v_a_3196_, v_x_3197_);
    crate::leanh::lean_dec(v_x_3197_);
    crate::leanh::lean_dec_ref(v_a_3196_);
    v_r_3199_ = crate::leanh::lean_box((v_res_3198_) as usize);
    return v_r_3199_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3(
    mut v_00_u03b2_3200_: *mut crate::leanh::LeanObject,
    mut v_data_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_data_3201_);
    return v___x_3202_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4(
    mut v_00_u03b2_3203_: *mut crate::leanh::LeanObject,
    mut v_a_3204_: *mut crate::leanh::LeanObject,
    mut v_b_3205_: *mut crate::leanh::LeanObject,
    mut v_x_3206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_3204_, v_b_3205_, v_x_3206_);
    return v___x_3207_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3208_: *mut crate::leanh::LeanObject,
    mut v_i_3209_: *mut crate::leanh::LeanObject,
    mut v_source_3210_: *mut crate::leanh::LeanObject,
    mut v_target_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3212_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v_i_3209_, v_source_3210_, v_target_3211_);
    return v___x_3212_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3213_: *mut crate::leanh::LeanObject,
    mut v_x_3214_: *mut crate::leanh::LeanObject,
    mut v_x_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_x_3214_, v_x_3215_);
    return v___x_3216_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(
    mut v_reified_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_originalExpr_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtAtoms_x27_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atoms_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomsAssignmentCache_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut v_val_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3254_: u8 = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3224_ = lean_st_ref_get(v_a_3218_);
                v_evalsAtCache_3225_ = crate::leanh::lean_ctor_get(v___x_3224_, 2);
                crate::leanh::lean_inc_ref(v_evalsAtCache_3225_);
                crate::leanh::lean_dec(v___x_3224_);
                v_originalExpr_3226_ = crate::leanh::lean_ctor_get(v_reified_3217_, 1);
                crate::leanh::lean_inc_ref(v_originalExpr_3226_);
                v_evalsAtAtoms_x27_3227_ = crate::leanh::lean_ctor_get(v_reified_3217_, 2);
                crate::leanh::lean_inc_ref(v_evalsAtAtoms_x27_3227_);
                crate::leanh::lean_dec_ref(v_reified_3217_);
                v___x_3228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_3225_, v_originalExpr_3226_);
                crate::leanh::lean_dec_ref(v_evalsAtCache_3225_);
                if crate::leanh::lean_obj_tag(v___x_3228_) == 0 {
                    crate::leanh::lean_inc(v_a_3222_);
                    crate::leanh::lean_inc_ref(v_a_3221_);
                    crate::leanh::lean_inc(v_a_3220_);
                    crate::leanh::lean_inc_ref(v_a_3219_);
                    crate::leanh::lean_inc(v_a_3218_);
                    v___x_3229_ = crate::leanh::lean_apply_6(
                        v_evalsAtAtoms_x27_3227_,
                        v_a_3218_,
                        v_a_3219_,
                        v_a_3220_,
                        v_a_3221_,
                        v_a_3222_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3229_) == 0 {
                        v_a_3230_ = crate::leanh::lean_ctor_get(v___x_3229_, 0);
                        v_isSharedCheck_3250_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3229_)) as u8;
                        if v_isSharedCheck_3250_ == 0 {
                            v___x_3232_ = v___x_3229_;
                            v_isShared_3233_ = v_isSharedCheck_3250_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3230_);
                            crate::leanh::lean_dec(v___x_3229_);
                            v___x_3232_ = crate::leanh::lean_box(0);
                            v_isShared_3233_ = v_isSharedCheck_3250_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_originalExpr_3226_);
                        return v___x_3229_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_evalsAtAtoms_x27_3227_);
                    crate::leanh::lean_dec_ref(v_originalExpr_3226_);
                    v_val_3251_ = crate::leanh::lean_ctor_get(v___x_3228_, 0);
                    v_isSharedCheck_3258_ = (!crate::leanh::lean_is_exclusive(v___x_3228_)) as u8;
                    if v_isSharedCheck_3258_ == 0 {
                        v___x_3253_ = v___x_3228_;
                        v_isShared_3254_ = v_isSharedCheck_3258_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3251_);
                        crate::leanh::lean_dec(v___x_3228_);
                        v___x_3253_ = crate::leanh::lean_box(0);
                        v_isShared_3254_ = v_isSharedCheck_3258_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3234_ = lean_st_ref_take(v_a_3218_);
                v_atoms_3235_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                v_atomsAssignmentCache_3236_ = crate::leanh::lean_ctor_get(v___x_3234_, 1);
                v_evalsAtCache_3237_ = crate::leanh::lean_ctor_get(v___x_3234_, 2);
                v_isSharedCheck_3249_ = (!crate::leanh::lean_is_exclusive(v___x_3234_)) as u8;
                if v_isSharedCheck_3249_ == 0 {
                    v___x_3239_ = v___x_3234_;
                    v_isShared_3240_ = v_isSharedCheck_3249_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_evalsAtCache_3237_);
                    crate::leanh::lean_inc(v_atomsAssignmentCache_3236_);
                    crate::leanh::lean_inc(v_atoms_3235_);
                    crate::leanh::lean_dec(v___x_3234_);
                    v___x_3239_ = crate::leanh::lean_box(0);
                    v_isShared_3240_ = v_isSharedCheck_3249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_3230_);
                v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_3237_, v_originalExpr_3226_, v_a_3230_);
                if v_isShared_3240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3239_, 2, v___x_3241_);
                    v___x_3243_ = v___x_3239_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_atoms_3235_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3248_,
                        1,
                        v_atomsAssignmentCache_3236_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 2, v___x_3241_);
                    v___x_3243_ = v_reuseFailAlloc_3248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3244_ = lean_st_ref_set(v_a_3218_, v___x_3243_);
                if v_isShared_3233_ == 0 {
                    v___x_3246_ = v___x_3232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3230_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3246_;
            }
            5 => {
                if v_isShared_3254_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3253_, 0);
                    v___x_3256_ = v___x_3253_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3257_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_val_3251_);
                    v___x_3256_ = v_reuseFailAlloc_3257_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(
    mut v_reified_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
    mut v_a_3264_: *mut crate::leanh::LeanObject,
    mut v_a_3265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(
        v_reified_3259_,
        v_a_3260_,
        v_a_3261_,
        v_a_3262_,
        v_a_3263_,
        v_a_3264_,
    );
    crate::leanh::lean_dec(v_a_3264_);
    crate::leanh::lean_dec_ref(v_a_3263_);
    crate::leanh::lean_dec(v_a_3262_);
    crate::leanh::lean_dec_ref(v_a_3261_);
    crate::leanh::lean_dec(v_a_3260_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
    mut v_reified_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
    mut v_a_3271_: *mut crate::leanh::LeanObject,
    mut v_a_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_originalExpr_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtAtoms_x27_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atoms_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomsAssignmentCache_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3299_: u8 = 0;
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut v_val_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3274_ = lean_st_ref_get(v_a_3268_);
                v_evalsAtCache_3275_ = crate::leanh::lean_ctor_get(v___x_3274_, 2);
                crate::leanh::lean_inc_ref(v_evalsAtCache_3275_);
                crate::leanh::lean_dec(v___x_3274_);
                v_originalExpr_3276_ = crate::leanh::lean_ctor_get(v_reified_3267_, 1);
                crate::leanh::lean_inc_ref(v_originalExpr_3276_);
                v_evalsAtAtoms_x27_3277_ = crate::leanh::lean_ctor_get(v_reified_3267_, 2);
                crate::leanh::lean_inc_ref(v_evalsAtAtoms_x27_3277_);
                crate::leanh::lean_dec_ref(v_reified_3267_);
                v___x_3278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_3275_, v_originalExpr_3276_);
                crate::leanh::lean_dec_ref(v_evalsAtCache_3275_);
                if crate::leanh::lean_obj_tag(v___x_3278_) == 0 {
                    crate::leanh::lean_inc(v_a_3272_);
                    crate::leanh::lean_inc_ref(v_a_3271_);
                    crate::leanh::lean_inc(v_a_3270_);
                    crate::leanh::lean_inc_ref(v_a_3269_);
                    crate::leanh::lean_inc(v_a_3268_);
                    v___x_3279_ = crate::leanh::lean_apply_6(
                        v_evalsAtAtoms_x27_3277_,
                        v_a_3268_,
                        v_a_3269_,
                        v_a_3270_,
                        v_a_3271_,
                        v_a_3272_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3279_) == 0 {
                        v_a_3280_ = crate::leanh::lean_ctor_get(v___x_3279_, 0);
                        v_isSharedCheck_3300_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3279_)) as u8;
                        if v_isSharedCheck_3300_ == 0 {
                            v___x_3282_ = v___x_3279_;
                            v_isShared_3283_ = v_isSharedCheck_3300_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3280_);
                            crate::leanh::lean_dec(v___x_3279_);
                            v___x_3282_ = crate::leanh::lean_box(0);
                            v_isShared_3283_ = v_isSharedCheck_3300_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_originalExpr_3276_);
                        return v___x_3279_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_evalsAtAtoms_x27_3277_);
                    crate::leanh::lean_dec_ref(v_originalExpr_3276_);
                    v_val_3301_ = crate::leanh::lean_ctor_get(v___x_3278_, 0);
                    v_isSharedCheck_3308_ = (!crate::leanh::lean_is_exclusive(v___x_3278_)) as u8;
                    if v_isSharedCheck_3308_ == 0 {
                        v___x_3303_ = v___x_3278_;
                        v_isShared_3304_ = v_isSharedCheck_3308_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3301_);
                        crate::leanh::lean_dec(v___x_3278_);
                        v___x_3303_ = crate::leanh::lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3308_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3284_ = lean_st_ref_take(v_a_3268_);
                v_atoms_3285_ = crate::leanh::lean_ctor_get(v___x_3284_, 0);
                v_atomsAssignmentCache_3286_ = crate::leanh::lean_ctor_get(v___x_3284_, 1);
                v_evalsAtCache_3287_ = crate::leanh::lean_ctor_get(v___x_3284_, 2);
                v_isSharedCheck_3299_ = (!crate::leanh::lean_is_exclusive(v___x_3284_)) as u8;
                if v_isSharedCheck_3299_ == 0 {
                    v___x_3289_ = v___x_3284_;
                    v_isShared_3290_ = v_isSharedCheck_3299_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_evalsAtCache_3287_);
                    crate::leanh::lean_inc(v_atomsAssignmentCache_3286_);
                    crate::leanh::lean_inc(v_atoms_3285_);
                    crate::leanh::lean_dec(v___x_3284_);
                    v___x_3289_ = crate::leanh::lean_box(0);
                    v_isShared_3290_ = v_isSharedCheck_3299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_3280_);
                v___x_3291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_3287_, v_originalExpr_3276_, v_a_3280_);
                if v_isShared_3290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3289_, 2, v___x_3291_);
                    v___x_3293_ = v___x_3289_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3298_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_atoms_3285_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3298_,
                        1,
                        v_atomsAssignmentCache_3286_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 2, v___x_3291_);
                    v___x_3293_ = v_reuseFailAlloc_3298_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3294_ = lean_st_ref_set(v_a_3268_, v___x_3293_);
                if v_isShared_3283_ == 0 {
                    v___x_3296_ = v___x_3282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3280_);
                    v___x_3296_ = v_reuseFailAlloc_3297_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3296_;
            }
            5 => {
                if v_isShared_3304_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3303_, 0);
                    v___x_3306_ = v___x_3303_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_val_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms___boxed(
    mut v_reified_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
        v_reified_3309_,
        v_a_3310_,
        v_a_3311_,
        v_a_3312_,
        v_a_3313_,
        v_a_3314_,
    );
    crate::leanh::lean_dec(v_a_3314_);
    crate::leanh::lean_dec_ref(v_a_3313_);
    crate::leanh::lean_dec(v_a_3312_);
    crate::leanh::lean_dec_ref(v_a_3311_);
    crate::leanh::lean_dec(v_a_3310_);
    return v_res_3316_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ = crate::leanh::lean_box(0);
    v___x_3318_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3319_ = lean_mk_array(v___x_3318_, v___x_3317_);
    return v___x_3319_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0_once),
        _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0,
    );
    v___x_3321_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3322_, 0, v___x_3321_);
    crate::leanh::lean_ctor_set(v___x_3322_, 1, v___x_3320_);
    return v___x_3322_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = crate::leanh::lean_box(0);
    v___x_3324_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1,
    );
    v___x_3325_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3325_, 0, v___x_3324_);
    crate::leanh::lean_ctor_set(v___x_3325_, 1, v___x_3323_);
    crate::leanh::lean_ctor_set(v___x_3325_, 2, v___x_3324_);
    return v___x_3325_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_run___redArg(
    mut v_m_3326_: *mut crate::leanh::LeanObject,
    mut v_a_3327_: *mut crate::leanh::LeanObject,
    mut v_a_3328_: *mut crate::leanh::LeanObject,
    mut v_a_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3332_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2,
                );
                v___x_3333_ = lean_st_mk_ref(v___x_3332_);
                crate::leanh::lean_inc(v_a_3330_);
                crate::leanh::lean_inc_ref(v_a_3329_);
                crate::leanh::lean_inc(v_a_3328_);
                crate::leanh::lean_inc_ref(v_a_3327_);
                crate::leanh::lean_inc(v___x_3333_);
                v___x_3334_ = crate::leanh::lean_apply_6(
                    v_m_3326_,
                    v___x_3333_,
                    v_a_3327_,
                    v_a_3328_,
                    v_a_3329_,
                    v_a_3330_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3334_) == 0 {
                    v_a_3335_ = crate::leanh::lean_ctor_get(v___x_3334_, 0);
                    v_isSharedCheck_3343_ = (!crate::leanh::lean_is_exclusive(v___x_3334_)) as u8;
                    if v_isSharedCheck_3343_ == 0 {
                        v___x_3337_ = v___x_3334_;
                        v_isShared_3338_ = v_isSharedCheck_3343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3335_);
                        crate::leanh::lean_dec(v___x_3334_);
                        v___x_3337_ = crate::leanh::lean_box(0);
                        v_isShared_3338_ = v_isSharedCheck_3343_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3333_);
                    return v___x_3334_;
                }
            }
            1 => {
                v___x_3339_ = lean_st_ref_get(v___x_3333_);
                crate::leanh::lean_dec(v___x_3333_);
                crate::leanh::lean_dec(v___x_3339_);
                if v_isShared_3338_ == 0 {
                    v___x_3341_ = v___x_3337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3335_);
                    v___x_3341_ = v_reuseFailAlloc_3342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_run___redArg___boxed(
    mut v_m_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(
        v_m_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_,
    );
    crate::leanh::lean_dec(v_a_3348_);
    crate::leanh::lean_dec_ref(v_a_3347_);
    crate::leanh::lean_dec(v_a_3346_);
    crate::leanh::lean_dec_ref(v_a_3345_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_run(
    mut v_00_u03b1_3351_: *mut crate::leanh::LeanObject,
    mut v_m_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(
        v_m_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_,
    );
    return v___x_3358_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_run___boxed(
    mut v_00_u03b1_3359_: *mut crate::leanh::LeanObject,
    mut v_m_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
    mut v_a_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3366_ = l_Lean_Meta_Tactic_BVDecide_M_run(
        v_00_u03b1_3359_,
        v_m_3360_,
        v_a_3361_,
        v_a_3362_,
        v_a_3363_,
        v_a_3364_,
    );
    crate::leanh::lean_dec(v_a_3364_);
    crate::leanh::lean_dec_ref(v_a_3363_);
    crate::leanh::lean_dec(v_a_3362_);
    crate::leanh::lean_dec_ref(v_a_3361_);
    return v_res_3366_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___redArg(
    mut v_hi_3367_: *mut crate::leanh::LeanObject,
    mut v_pivot_3368_: *mut crate::leanh::LeanObject,
    mut v_as_3369_: *mut crate::leanh::LeanObject,
    mut v_i_3370_: *mut crate::leanh::LeanObject,
    mut v_k_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomNumber_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomNumber_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: u8 = 0;
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3372_ = lean_nat_dec_lt(v_k_3371_, v_hi_3367_);
                if v___x_3372_ == 0 {
                    crate::leanh::lean_dec(v_k_3371_);
                    v___x_3373_ = lean_array_fswap(v_as_3369_, v_i_3370_, v_hi_3367_);
                    v___x_3374_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3374_, 0, v_i_3370_);
                    crate::leanh::lean_ctor_set(v___x_3374_, 1, v___x_3373_);
                    return v___x_3374_;
                } else {
                    v___x_3375_ = lean_array_fget_borrowed(v_as_3369_, v_k_3371_);
                    v_snd_3376_ = crate::leanh::lean_ctor_get(v___x_3375_, 1);
                    v_snd_3377_ = crate::leanh::lean_ctor_get(v_pivot_3368_, 1);
                    v_atomNumber_3378_ = crate::leanh::lean_ctor_get(v_snd_3376_, 1);
                    v_atomNumber_3379_ = crate::leanh::lean_ctor_get(v_snd_3377_, 1);
                    v___x_3380_ = lean_nat_dec_lt(v_atomNumber_3378_, v_atomNumber_3379_);
                    if v___x_3380_ == 0 {
                        v___x_3381_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3382_ = lean_nat_add(v_k_3371_, v___x_3381_);
                        crate::leanh::lean_dec(v_k_3371_);
                        v_k_3371_ = v___x_3382_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3384_ = lean_array_fswap(v_as_3369_, v_i_3370_, v_k_3371_);
                        v___x_3385_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3386_ = lean_nat_add(v_i_3370_, v___x_3385_);
                        crate::leanh::lean_dec(v_i_3370_);
                        v___x_3387_ = lean_nat_add(v_k_3371_, v___x_3385_);
                        crate::leanh::lean_dec(v_k_3371_);
                        v_as_3369_ = v___x_3384_;
                        v_i_3370_ = v___x_3386_;
                        v_k_3371_ = v___x_3387_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___redArg___boxed(
    mut v_hi_3389_: *mut crate::leanh::LeanObject,
    mut v_pivot_3390_: *mut crate::leanh::LeanObject,
    mut v_as_3391_: *mut crate::leanh::LeanObject,
    mut v_i_3392_: *mut crate::leanh::LeanObject,
    mut v_k_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___redArg(v_hi_3389_, v_pivot_3390_, v_as_3391_, v_i_3392_, v_k_3393_);
    crate::leanh::lean_dec_ref(v_pivot_3390_);
    crate::leanh::lean_dec(v_hi_3389_);
    return v_res_3394_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___lam__0(
    mut v_x1_3395_: *mut crate::leanh::LeanObject,
    mut v_x2_3396_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_snd_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomNumber_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomNumber_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    v_snd_3397_ = crate::leanh::lean_ctor_get(v_x1_3395_, 1);
    v_snd_3398_ = crate::leanh::lean_ctor_get(v_x2_3396_, 1);
    v_atomNumber_3399_ = crate::leanh::lean_ctor_get(v_snd_3397_, 1);
    v_atomNumber_3400_ = crate::leanh::lean_ctor_get(v_snd_3398_, 1);
    v___x_3401_ = lean_nat_dec_lt(v_atomNumber_3399_, v_atomNumber_3400_);
    return v___x_3401_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___lam__0___boxed(
    mut v_x1_3402_: *mut crate::leanh::LeanObject,
    mut v_x2_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3404_: u8 = 0;
    let mut v_r_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___lam__0(v_x1_3402_, v_x2_3403_);
    crate::leanh::lean_dec_ref(v_x2_3403_);
    crate::leanh::lean_dec_ref(v_x1_3402_);
    v_r_3405_ = crate::leanh::lean_box((v_res_3404_) as usize);
    return v_r_3405_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg(
    mut v_n_3406_: *mut crate::leanh::LeanObject,
    mut v_as_3407_: *mut crate::leanh::LeanObject,
    mut v_lo_3408_: *mut crate::leanh::LeanObject,
    mut v_hi_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: u8 = 0;
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3421_ = lean_nat_dec_lt(v_lo_3408_, v_hi_3409_);
                if v___x_3421_ == 0 {
                    crate::leanh::lean_dec(v_lo_3408_);
                    return v_as_3407_;
                } else {
                    v___x_3422_ = lean_nat_add(v_lo_3408_, v_hi_3409_);
                    v___x_3423_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3424_ = lean_nat_shiftr(v___x_3422_, v___x_3423_);
                    crate::leanh::lean_dec(v___x_3422_);
                    v___x_3437_ = lean_array_fget_borrowed(v_as_3407_, v_mid_3424_);
                    v___x_3438_ = lean_array_fget_borrowed(v_as_3407_, v_lo_3408_);
                    v___x_3439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___lam__0(v___x_3437_, v___x_3438_);
                    if v___x_3439_ == 0 {
                        v___y_3432_ = v_as_3407_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3440_ = lean_array_fswap(v_as_3407_, v_lo_3408_, v_mid_3424_);
                        v___y_3432_ = v___x_3440_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3412_ = lean_array_fget(v___y_3411_, v_hi_3409_);
                crate::leanh::lean_inc_n(v_lo_3408_, 2);
                v___x_3413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___redArg(v_hi_3409_, v_pivot_3412_, v___y_3411_, v_lo_3408_, v_lo_3408_);
                crate::leanh::lean_dec(v_pivot_3412_);
                v_fst_3414_ = crate::leanh::lean_ctor_get(v___x_3413_, 0);
                crate::leanh::lean_inc(v_fst_3414_);
                v_snd_3415_ = crate::leanh::lean_ctor_get(v___x_3413_, 1);
                crate::leanh::lean_inc(v_snd_3415_);
                crate::leanh::lean_dec_ref(v___x_3413_);
                v___x_3416_ = lean_nat_dec_le(v_hi_3409_, v_fst_3414_);
                if v___x_3416_ == 0 {
                    v___x_3417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg(v_n_3406_, v_snd_3415_, v_lo_3408_, v_fst_3414_);
                    v___x_3418_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3419_ = lean_nat_add(v_fst_3414_, v___x_3418_);
                    crate::leanh::lean_dec(v_fst_3414_);
                    v_as_3407_ = v___x_3417_;
                    v_lo_3408_ = v___x_3419_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3414_);
                    crate::leanh::lean_dec(v_lo_3408_);
                    return v_snd_3415_;
                }
            }
            2 => {
                v___x_3427_ = lean_array_fget_borrowed(v___y_3426_, v_mid_3424_);
                v___x_3428_ = lean_array_fget_borrowed(v___y_3426_, v_hi_3409_);
                v___x_3429_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___lam__0(v___x_3427_, v___x_3428_);
                if v___x_3429_ == 0 {
                    crate::leanh::lean_dec(v_mid_3424_);
                    v___y_3411_ = v___y_3426_;
                    state = 1;
                    continue;
                } else {
                    v___x_3430_ = lean_array_fswap(v___y_3426_, v_mid_3424_, v_hi_3409_);
                    crate::leanh::lean_dec(v_mid_3424_);
                    v___y_3411_ = v___x_3430_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3433_ = lean_array_fget_borrowed(v___y_3432_, v_hi_3409_);
                v___x_3434_ = lean_array_fget_borrowed(v___y_3432_, v_lo_3408_);
                v___x_3435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___lam__0(v___x_3433_, v___x_3434_);
                if v___x_3435_ == 0 {
                    v___y_3426_ = v___y_3432_;
                    state = 2;
                    continue;
                } else {
                    v___x_3436_ = lean_array_fswap(v___y_3432_, v_lo_3408_, v_hi_3409_);
                    v___y_3426_ = v___x_3436_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg___boxed(
    mut v_n_3441_: *mut crate::leanh::LeanObject,
    mut v_as_3442_: *mut crate::leanh::LeanObject,
    mut v_lo_3443_: *mut crate::leanh::LeanObject,
    mut v_hi_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg(v_n_3441_, v_as_3442_, v_lo_3443_, v_hi_3444_);
    crate::leanh::lean_dec(v_hi_3444_);
    crate::leanh::lean_dec(v_n_3441_);
    return v_res_3445_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2(
    mut v_x_3446_: *mut crate::leanh::LeanObject,
    mut v_x_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3447_) == 0 {
                    return v_x_3446_;
                } else {
                    v_key_3448_ = crate::leanh::lean_ctor_get(v_x_3447_, 0);
                    v_value_3449_ = crate::leanh::lean_ctor_get(v_x_3447_, 1);
                    v_tail_3450_ = crate::leanh::lean_ctor_get(v_x_3447_, 2);
                    crate::leanh::lean_inc(v_value_3449_);
                    crate::leanh::lean_inc(v_key_3448_);
                    v___x_3451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3451_, 0, v_key_3448_);
                    crate::leanh::lean_ctor_set(v___x_3451_, 1, v_value_3449_);
                    v___x_3452_ = lean_array_push(v_x_3446_, v___x_3451_);
                    v_x_3446_ = v___x_3452_;
                    v_x_3447_ = v_tail_3450_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___boxed(
    mut v_x_3454_: *mut crate::leanh::LeanObject,
    mut v_x_3455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3456_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2(
            v_x_3454_, v_x_3455_,
        );
    crate::leanh::lean_dec(v_x_3455_);
    return v_res_3456_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__3(
    mut v_as_3457_: *mut crate::leanh::LeanObject,
    mut v_i_3458_: usize,
    mut v_stop_3459_: usize,
    mut v_b_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: usize = 0;
    let mut v___x_3465_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3461_ = lean_usize_dec_eq(v_i_3458_, v_stop_3459_);
                if v___x_3461_ == 0 {
                    v___x_3462_ = lean_array_uget_borrowed(v_as_3457_, v_i_3458_);
                    v___x_3463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2(v_b_3460_, v___x_3462_);
                    v___x_3464_ = 1usize;
                    v___x_3465_ = lean_usize_add(v_i_3458_, v___x_3464_);
                    v_i_3458_ = v___x_3465_;
                    v_b_3460_ = v___x_3463_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3460_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__3___boxed(
    mut v_as_3467_: *mut crate::leanh::LeanObject,
    mut v_i_3468_: *mut crate::leanh::LeanObject,
    mut v_stop_3469_: *mut crate::leanh::LeanObject,
    mut v_b_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3471_: usize = 0;
    let mut v_stop_boxed_3472_: usize = 0;
    let mut v_res_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3471_ = crate::leanh::lean_unbox_usize(v_i_3468_);
    crate::leanh::lean_dec(v_i_3468_);
    v_stop_boxed_3472_ = crate::leanh::lean_unbox_usize(v_stop_3469_);
    crate::leanh::lean_dec(v_stop_3469_);
    v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__3(v_as_3467_, v_i_boxed_3471_, v_stop_boxed_3472_, v_b_3470_);
    crate::leanh::lean_dec_ref(v_as_3467_);
    return v_res_3473_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(
    mut v_sz_3474_: usize,
    mut v_i_3475_: usize,
    mut v_bs_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3477_: u8 = 0;
    let mut v_v_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v_width_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3477_ = lean_usize_dec_lt(v_i_3475_, v_sz_3474_);
                if v___x_3477_ == 0 {
                    return v_bs_3476_;
                } else {
                    v_v_3478_ = lean_array_uget(v_bs_3476_, v_i_3475_);
                    v_snd_3479_ = crate::leanh::lean_ctor_get(v_v_3478_, 1);
                    v_fst_3480_ = crate::leanh::lean_ctor_get(v_v_3478_, 0);
                    v_isSharedCheck_3494_ = (!crate::leanh::lean_is_exclusive(v_v_3478_)) as u8;
                    if v_isSharedCheck_3494_ == 0 {
                        v___x_3482_ = v_v_3478_;
                        v_isShared_3483_ = v_isSharedCheck_3494_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3479_);
                        crate::leanh::lean_inc(v_fst_3480_);
                        crate::leanh::lean_dec(v_v_3478_);
                        v___x_3482_ = crate::leanh::lean_box(0);
                        v_isShared_3483_ = v_isSharedCheck_3494_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_width_3484_ = crate::leanh::lean_ctor_get(v_snd_3479_, 0);
                crate::leanh::lean_inc(v_width_3484_);
                crate::leanh::lean_dec(v_snd_3479_);
                v___x_3485_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3486_ = lean_array_uset(v_bs_3476_, v_i_3475_, v___x_3485_);
                if v_isShared_3483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3482_, 1, v_fst_3480_);
                    crate::leanh::lean_ctor_set(v___x_3482_, 0, v_width_3484_);
                    v___x_3488_ = v___x_3482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3493_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_width_3484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_fst_3480_);
                    v___x_3488_ = v_reuseFailAlloc_3493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3489_ = 1usize;
                v___x_3490_ = lean_usize_add(v_i_3475_, v___x_3489_);
                v___x_3491_ = lean_array_uset(v_bs_x27_3486_, v_i_3475_, v___x_3488_);
                v_i_3475_ = v___x_3490_;
                v_bs_3476_ = v___x_3491_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0___boxed(
    mut v_sz_3495_: *mut crate::leanh::LeanObject,
    mut v_i_3496_: *mut crate::leanh::LeanObject,
    mut v_bs_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3498_: usize = 0;
    let mut v_i_boxed_3499_: usize = 0;
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3498_ = crate::leanh::lean_unbox_usize(v_sz_3495_);
    crate::leanh::lean_dec(v_sz_3495_);
    v_i_boxed_3499_ = crate::leanh::lean_unbox_usize(v_i_3496_);
    crate::leanh::lean_dec(v_i_3496_);
    v_res_3500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(v_sz_boxed_3498_, v_i_boxed_3499_, v_bs_3497_);
    return v_res_3500_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(
    mut v_a_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3506_: usize = 0;
    let mut v___x_3507_: usize = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v___y_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: u8 = 0;
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v_atoms_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: usize = 0;
    let mut v___x_3539_: usize = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: usize = 0;
    let mut v___x_3542_: usize = 0;
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3503_ = lean_st_ref_get(v_a_3501_);
                v_atoms_3530_ = crate::leanh::lean_ctor_get(v___x_3503_, 0);
                crate::leanh::lean_inc_ref(v_atoms_3530_);
                crate::leanh::lean_dec(v___x_3503_);
                v_size_3531_ = crate::leanh::lean_ctor_get(v_atoms_3530_, 0);
                crate::leanh::lean_inc(v_size_3531_);
                v_buckets_3532_ = crate::leanh::lean_ctor_get(v_atoms_3530_, 1);
                crate::leanh::lean_inc_ref(v_buckets_3532_);
                crate::leanh::lean_dec_ref(v_atoms_3530_);
                v___x_3533_ = lean_mk_empty_array_with_capacity(v_size_3531_);
                crate::leanh::lean_dec(v_size_3531_);
                v___x_3534_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3535_ = lean_array_get_size(v_buckets_3532_);
                v___x_3536_ = lean_nat_dec_lt(v___x_3534_, v___x_3535_);
                if v___x_3536_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_3532_);
                    v___y_3523_ = v___x_3533_;
                    state = 4;
                    continue;
                } else {
                    v___x_3537_ = lean_nat_dec_le(v___x_3535_, v___x_3535_);
                    if v___x_3537_ == 0 {
                        if v___x_3536_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_3532_);
                            v___y_3523_ = v___x_3533_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3538_ = 0usize;
                            v___x_3539_ = lean_usize_of_nat(v___x_3535_);
                            v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__3(v_buckets_3532_, v___x_3538_, v___x_3539_, v___x_3533_);
                            crate::leanh::lean_dec_ref(v_buckets_3532_);
                            v___y_3523_ = v___x_3540_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_3541_ = 0usize;
                        v___x_3542_ = lean_usize_of_nat(v___x_3535_);
                        v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__3(v_buckets_3532_, v___x_3541_, v___x_3542_, v___x_3533_);
                        crate::leanh::lean_dec_ref(v_buckets_3532_);
                        v___y_3523_ = v___x_3543_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_3506_ = lean_array_size(v___y_3505_);
                v___x_3507_ = 0usize;
                v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(v_sz_3506_, v___x_3507_, v___y_3505_);
                v___x_3509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3509_, 0, v___x_3508_);
                return v___x_3509_;
            }
            2 => {
                v___x_3515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg(v___y_3513_, v___y_3512_, v___y_3511_, v___y_3514_);
                crate::leanh::lean_dec(v___y_3514_);
                crate::leanh::lean_dec(v___y_3513_);
                v___y_3505_ = v___x_3515_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3521_ = lean_nat_dec_le(v___y_3520_, v___y_3518_);
                if v___x_3521_ == 0 {
                    crate::leanh::lean_dec(v___y_3518_);
                    crate::leanh::lean_inc(v___y_3520_);
                    v___y_3511_ = v___y_3520_;
                    v___y_3512_ = v___y_3517_;
                    v___y_3513_ = v___y_3519_;
                    v___y_3514_ = v___y_3520_;
                    state = 2;
                    continue;
                } else {
                    v___y_3511_ = v___y_3520_;
                    v___y_3512_ = v___y_3517_;
                    v___y_3513_ = v___y_3519_;
                    v___y_3514_ = v___y_3518_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_3524_ = lean_array_get_size(v___y_3523_);
                v___x_3525_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3526_ = lean_nat_dec_eq(v___x_3524_, v___x_3525_);
                if v___x_3526_ == 0 {
                    v___x_3527_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3528_ = lean_nat_sub(v___x_3524_, v___x_3527_);
                    v___x_3529_ = lean_nat_dec_le(v___x_3525_, v___x_3528_);
                    if v___x_3529_ == 0 {
                        crate::leanh::lean_inc(v___x_3528_);
                        v___y_3517_ = v___y_3523_;
                        v___y_3518_ = v___x_3528_;
                        v___y_3519_ = v___x_3524_;
                        v___y_3520_ = v___x_3528_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3517_ = v___y_3523_;
                        v___y_3518_ = v___x_3528_;
                        v___y_3519_ = v___x_3524_;
                        v___y_3520_ = v___x_3525_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_3505_ = v___y_3523_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg___boxed(
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3546_ = l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(v_a_3544_);
    crate::leanh::lean_dec(v_a_3544_);
    return v_res_3546_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_atoms(
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(v_a_3547_);
    return v___x_3553_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_atoms___boxed(
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3560_ =
        l_Lean_Meta_Tactic_BVDecide_M_atoms(v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
    crate::leanh::lean_dec(v_a_3558_);
    crate::leanh::lean_dec_ref(v_a_3557_);
    crate::leanh::lean_dec(v_a_3556_);
    crate::leanh::lean_dec_ref(v_a_3555_);
    crate::leanh::lean_dec(v_a_3554_);
    return v_res_3560_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1(
    mut v_n_3561_: *mut crate::leanh::LeanObject,
    mut v_as_3562_: *mut crate::leanh::LeanObject,
    mut v_lo_3563_: *mut crate::leanh::LeanObject,
    mut v_hi_3564_: *mut crate::leanh::LeanObject,
    mut v_w_3565_: *mut crate::leanh::LeanObject,
    mut v_hlo_3566_: *mut crate::leanh::LeanObject,
    mut v_hhi_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___redArg(v_n_3561_, v_as_3562_, v_lo_3563_, v_hi_3564_);
    return v___x_3568_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___boxed(
    mut v_n_3569_: *mut crate::leanh::LeanObject,
    mut v_as_3570_: *mut crate::leanh::LeanObject,
    mut v_lo_3571_: *mut crate::leanh::LeanObject,
    mut v_hi_3572_: *mut crate::leanh::LeanObject,
    mut v_w_3573_: *mut crate::leanh::LeanObject,
    mut v_hlo_3574_: *mut crate::leanh::LeanObject,
    mut v_hhi_3575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1(v_n_3569_, v_as_3570_, v_lo_3571_, v_hi_3572_, v_w_3573_, v_hlo_3574_, v_hhi_3575_);
    crate::leanh::lean_dec(v_hi_3572_);
    crate::leanh::lean_dec(v_n_3569_);
    return v_res_3576_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1(
    mut v_n_3577_: *mut crate::leanh::LeanObject,
    mut v_lo_3578_: *mut crate::leanh::LeanObject,
    mut v_hi_3579_: *mut crate::leanh::LeanObject,
    mut v_hhi_3580_: *mut crate::leanh::LeanObject,
    mut v_pivot_3581_: *mut crate::leanh::LeanObject,
    mut v_as_3582_: *mut crate::leanh::LeanObject,
    mut v_i_3583_: *mut crate::leanh::LeanObject,
    mut v_k_3584_: *mut crate::leanh::LeanObject,
    mut v_ilo_3585_: *mut crate::leanh::LeanObject,
    mut v_ik_3586_: *mut crate::leanh::LeanObject,
    mut v_w_3587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___redArg(v_hi_3579_, v_pivot_3581_, v_as_3582_, v_i_3583_, v_k_3584_);
    return v___x_3588_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___boxed(
    mut v_n_3589_: *mut crate::leanh::LeanObject,
    mut v_lo_3590_: *mut crate::leanh::LeanObject,
    mut v_hi_3591_: *mut crate::leanh::LeanObject,
    mut v_hhi_3592_: *mut crate::leanh::LeanObject,
    mut v_pivot_3593_: *mut crate::leanh::LeanObject,
    mut v_as_3594_: *mut crate::leanh::LeanObject,
    mut v_i_3595_: *mut crate::leanh::LeanObject,
    mut v_k_3596_: *mut crate::leanh::LeanObject,
    mut v_ilo_3597_: *mut crate::leanh::LeanObject,
    mut v_ik_3598_: *mut crate::leanh::LeanObject,
    mut v_w_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1(v_n_3589_, v_lo_3590_, v_hi_3591_, v_hhi_3592_, v_pivot_3593_, v_as_3594_, v_i_3595_, v_k_3596_, v_ilo_3597_, v_ik_3598_, v_w_3599_);
    crate::leanh::lean_dec_ref(v_pivot_3593_);
    crate::leanh::lean_dec(v_hi_3591_);
    crate::leanh::lean_dec(v_lo_3590_);
    crate::leanh::lean_dec(v_n_3589_);
    return v_res_3600_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0(
    mut v___x_3602_: *mut crate::leanh::LeanObject,
    mut v___x_3603_: *mut crate::leanh::LeanObject,
    mut v___x_3604_: *mut crate::leanh::LeanObject,
    mut v___x_3605_: *mut crate::leanh::LeanObject,
    mut v___x_3606_: *mut crate::leanh::LeanObject,
    mut v___x_3607_: *mut crate::leanh::LeanObject,
    mut v_x_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3609_ = crate::leanh::lean_ctor_get(v_x_3608_, 0);
    crate::leanh::lean_inc(v_fst_3609_);
    v_snd_3610_ = crate::leanh::lean_ctor_get(v_x_3608_, 1);
    crate::leanh::lean_inc(v_snd_3610_);
    crate::leanh::lean_dec_ref(v_x_3608_);
    v___x_3611_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0;
    v___x_3612_ = l_Lean_Name_mkStr6(
        v___x_3602_,
        v___x_3603_,
        v___x_3604_,
        v___x_3605_,
        v___x_3606_,
        v___x_3611_,
    );
    v___x_3613_ = l_Lean_mkConst(v___x_3612_, v___x_3607_);
    v___x_3614_ = l_Lean_mkNatLit(v_fst_3609_);
    v___x_3615_ = l_Lean_mkAppB(v___x_3613_, v___x_3614_, v_snd_3610_);
    return v___x_3615_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(
    mut v_msgData_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ = lean_st_ref_get(v___y_3620_);
    v_env_3623_ = crate::leanh::lean_ctor_get(v___x_3622_, 0);
    crate::leanh::lean_inc_ref(v_env_3623_);
    crate::leanh::lean_dec(v___x_3622_);
    v___x_3624_ = lean_st_ref_get(v___y_3618_);
    v_mctx_3625_ = crate::leanh::lean_ctor_get(v___x_3624_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3625_);
    crate::leanh::lean_dec(v___x_3624_);
    v_lctx_3626_ = crate::leanh::lean_ctor_get(v___y_3617_, 2);
    v_options_3627_ = crate::leanh::lean_ctor_get(v___y_3619_, 2);
    crate::leanh::lean_inc_ref(v_options_3627_);
    crate::leanh::lean_inc_ref(v_lctx_3626_);
    v___x_3628_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3628_, 0, v_env_3623_);
    crate::leanh::lean_ctor_set(v___x_3628_, 1, v_mctx_3625_);
    crate::leanh::lean_ctor_set(v___x_3628_, 2, v_lctx_3626_);
    crate::leanh::lean_ctor_set(v___x_3628_, 3, v_options_3627_);
    v___x_3629_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3629_, 0, v___x_3628_);
    crate::leanh::lean_ctor_set(v___x_3629_, 1, v_msgData_3616_);
    v___x_3630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3630_, 0, v___x_3629_);
    return v___x_3630_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0___boxed(
    mut v_msgData_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3637_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msgData_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
    crate::leanh::lean_dec(v___y_3635_);
    crate::leanh::lean_dec_ref(v___y_3634_);
    crate::leanh::lean_dec(v___y_3633_);
    crate::leanh::lean_dec_ref(v___y_3632_);
    return v_res_3637_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(
    mut v_msg_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3649_: u8 = 0;
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3644_ = crate::leanh::lean_ctor_get(v___y_3641_, 5);
                v___x_3645_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
                v_a_3646_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                v_isSharedCheck_3654_ = (!crate::leanh::lean_is_exclusive(v___x_3645_)) as u8;
                if v_isSharedCheck_3654_ == 0 {
                    v___x_3648_ = v___x_3645_;
                    v_isShared_3649_ = v_isSharedCheck_3654_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3646_);
                    crate::leanh::lean_dec(v___x_3645_);
                    v___x_3648_ = crate::leanh::lean_box(0);
                    v_isShared_3649_ = v_isSharedCheck_3654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3644_);
                v___x_3650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3650_, 0, v_ref_3644_);
                crate::leanh::lean_ctor_set(v___x_3650_, 1, v_a_3646_);
                if v_isShared_3649_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3648_, 1);
                    crate::leanh::lean_ctor_set(v___x_3648_, 0, v___x_3650_);
                    v___x_3652_ = v___x_3648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
                    v___x_3652_ = v_reuseFailAlloc_3653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg___boxed(
    mut v_msg_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3661_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
    crate::leanh::lean_dec(v___y_3659_);
    crate::leanh::lean_dec_ref(v___y_3658_);
    crate::leanh::lean_dec(v___y_3657_);
    crate::leanh::lean_dec_ref(v___y_3656_);
    return v_res_3661_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0;
    v___x_3664_ = l_Lean_stringToMessageData(v___x_3663_);
    return v___x_3664_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = crate::leanh::lean_box(0);
    v___x_3680_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3;
    v___x_3681_ = l_Lean_mkConst(v___x_3680_, v___x_3679_);
    return v___x_3681_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atoms_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalsAtCache_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3722_: u8 = 0;
    let mut v_unused_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut v_isSharedCheck_3725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3688_ = l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(v_a_3682_);
                v_a_3689_ = crate::leanh::lean_ctor_get(v___x_3688_, 0);
                v_isSharedCheck_3725_ = (!crate::leanh::lean_is_exclusive(v___x_3688_)) as u8;
                if v_isSharedCheck_3725_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    v_isShared_3692_ = v_isSharedCheck_3725_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3689_);
                    crate::leanh::lean_dec(v___x_3688_);
                    v___x_3691_ = crate::leanh::lean_box(0);
                    v_isShared_3692_ = v_isSharedCheck_3725_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3693_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3694_ = lean_array_get_size(v_a_3689_);
                v___x_3695_ = lean_nat_dec_lt(v___x_3693_, v___x_3694_);
                if v___x_3695_ == 0 {
                    crate::leanh::lean_del_object(v___x_3691_);
                    crate::leanh::lean_dec(v_a_3689_);
                    v___x_3696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1);
                    v___x_3697_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v___x_3696_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
                    return v___x_3697_;
                } else {
                    v___x_3698_ = l_Lean_RArray_ofArray___redArg(v_a_3689_);
                    v___f_3699_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4;
                    v___x_3700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5);
                    v___x_3701_ = l_Lean_RArray_toExpr___redArg(
                        v___x_3700_,
                        v___f_3699_,
                        v___x_3698_,
                        v_a_3683_,
                        v_a_3684_,
                        v_a_3685_,
                        v_a_3686_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3701_) == 0 {
                        v_a_3702_ = crate::leanh::lean_ctor_get(v___x_3701_, 0);
                        v_isSharedCheck_3724_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3701_)) as u8;
                        if v_isSharedCheck_3724_ == 0 {
                            v___x_3704_ = v___x_3701_;
                            v_isShared_3705_ = v_isSharedCheck_3724_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3702_);
                            crate::leanh::lean_dec(v___x_3701_);
                            v___x_3704_ = crate::leanh::lean_box(0);
                            v_isShared_3705_ = v_isSharedCheck_3724_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3691_);
                        return v___x_3701_;
                    }
                }
            }
            2 => {
                v___x_3706_ = lean_st_ref_take(v_a_3682_);
                v_atoms_3707_ = crate::leanh::lean_ctor_get(v___x_3706_, 0);
                v_evalsAtCache_3708_ = crate::leanh::lean_ctor_get(v___x_3706_, 2);
                v_isSharedCheck_3722_ = (!crate::leanh::lean_is_exclusive(v___x_3706_)) as u8;
                if v_isSharedCheck_3722_ == 0 {
                    v_unused_3723_ = crate::leanh::lean_ctor_get(v___x_3706_, 1);
                    crate::leanh::lean_dec(v_unused_3723_);
                    v___x_3710_ = v___x_3706_;
                    v_isShared_3711_ = v_isSharedCheck_3722_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_evalsAtCache_3708_);
                    crate::leanh::lean_inc(v_atoms_3707_);
                    crate::leanh::lean_dec(v___x_3706_);
                    v___x_3710_ = crate::leanh::lean_box(0);
                    v_isShared_3711_ = v_isSharedCheck_3722_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_3702_);
                if v_isShared_3692_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3691_, 1);
                    crate::leanh::lean_ctor_set(v___x_3691_, 0, v_a_3702_);
                    v___x_3713_ = v___x_3691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3702_);
                    v___x_3713_ = v_reuseFailAlloc_3721_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3710_, 1, v___x_3713_);
                    v___x_3715_ = v___x_3710_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3720_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_atoms_3707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 1, v___x_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 2, v_evalsAtCache_3708_);
                    v___x_3715_ = v_reuseFailAlloc_3720_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3716_ = lean_st_ref_set(v_a_3682_, v___x_3715_);
                if v_isShared_3705_ == 0 {
                    v___x_3718_ = v___x_3704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3702_);
                    v___x_3718_ = v_reuseFailAlloc_3719_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___boxed(
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
    crate::leanh::lean_dec(v_a_3730_);
    crate::leanh::lean_dec_ref(v_a_3729_);
    crate::leanh::lean_dec(v_a_3728_);
    crate::leanh::lean_dec_ref(v_a_3727_);
    crate::leanh::lean_dec(v_a_3726_);
    return v_res_3732_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0(
    mut v_00_u03b1_3733_: *mut crate::leanh::LeanObject,
    mut v_msg_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
    mut v___y_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3741_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_3734_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
    return v___x_3741_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___boxed(
    mut v_00_u03b1_3742_: *mut crate::leanh::LeanObject,
    mut v_msg_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0(v_00_u03b1_3742_, v_msg_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
    crate::leanh::lean_dec(v___y_3748_);
    crate::leanh::lean_dec_ref(v___y_3747_);
    crate::leanh::lean_dec(v___y_3746_);
    crate::leanh::lean_dec_ref(v___y_3745_);
    crate::leanh::lean_dec(v___y_3744_);
    return v_res_3750_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(
    mut v_a_3751_: *mut crate::leanh::LeanObject,
    mut v_a_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
    mut v_a_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomsAssignmentCache_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3757_ = lean_st_ref_get(v_a_3751_);
                v_atomsAssignmentCache_3758_ = crate::leanh::lean_ctor_get(v___x_3757_, 1);
                crate::leanh::lean_inc(v_atomsAssignmentCache_3758_);
                crate::leanh::lean_dec(v___x_3757_);
                if crate::leanh::lean_obj_tag(v_atomsAssignmentCache_3758_) == 0 {
                    v___x_3759_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
                    return v___x_3759_;
                } else {
                    v_val_3760_ = crate::leanh::lean_ctor_get(v_atomsAssignmentCache_3758_, 0);
                    v_isSharedCheck_3767_ =
                        (!crate::leanh::lean_is_exclusive(v_atomsAssignmentCache_3758_)) as u8;
                    if v_isSharedCheck_3767_ == 0 {
                        v___x_3762_ = v_atomsAssignmentCache_3758_;
                        v_isShared_3763_ = v_isSharedCheck_3767_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3760_);
                        crate::leanh::lean_dec(v_atomsAssignmentCache_3758_);
                        v___x_3762_ = crate::leanh::lean_box(0);
                        v_isShared_3763_ = v_isSharedCheck_3767_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3763_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3762_, 0);
                    v___x_3765_ = v___x_3762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3766_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_val_3760_);
                    v___x_3765_ = v_reuseFailAlloc_3766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment___boxed(
    mut v_a_3768_: *mut crate::leanh::LeanObject,
    mut v_a_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_a_3771_: *mut crate::leanh::LeanObject,
    mut v_a_3772_: *mut crate::leanh::LeanObject,
    mut v_a_3773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3774_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(
        v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_,
    );
    crate::leanh::lean_dec(v_a_3772_);
    crate::leanh::lean_dec_ref(v_a_3771_);
    crate::leanh::lean_dec(v_a_3770_);
    crate::leanh::lean_dec_ref(v_a_3769_);
    crate::leanh::lean_dec(v_a_3768_);
    return v_res_3774_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3775_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3775_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(
    mut v_msg_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v_toFunctor_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___f_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v_toFunctor_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v___f_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523__overap_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_unused_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut v_unused_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v_unused_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_unused_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3787_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0_once), _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0);
                v___x_3788_ = l_StateRefT_x27_instMonad___redArg(v___x_3787_);
                v_toApplicative_3789_ = crate::leanh::lean_ctor_get(v___x_3788_, 0);
                v_isSharedCheck_3851_ = (!crate::leanh::lean_is_exclusive(v___x_3788_)) as u8;
                if v_isSharedCheck_3851_ == 0 {
                    v_unused_3852_ = crate::leanh::lean_ctor_get(v___x_3788_, 1);
                    crate::leanh::lean_dec(v_unused_3852_);
                    v___x_3791_ = v___x_3788_;
                    v_isShared_3792_ = v_isSharedCheck_3851_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3789_);
                    crate::leanh::lean_dec(v___x_3788_);
                    v___x_3791_ = crate::leanh::lean_box(0);
                    v_isShared_3792_ = v_isSharedCheck_3851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3793_ = crate::leanh::lean_ctor_get(v_toApplicative_3789_, 0);
                v_toSeq_3794_ = crate::leanh::lean_ctor_get(v_toApplicative_3789_, 2);
                v_toSeqLeft_3795_ = crate::leanh::lean_ctor_get(v_toApplicative_3789_, 3);
                v_toSeqRight_3796_ = crate::leanh::lean_ctor_get(v_toApplicative_3789_, 4);
                v_isSharedCheck_3849_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3789_)) as u8;
                if v_isSharedCheck_3849_ == 0 {
                    v_unused_3850_ = crate::leanh::lean_ctor_get(v_toApplicative_3789_, 1);
                    crate::leanh::lean_dec(v_unused_3850_);
                    v___x_3798_ = v_toApplicative_3789_;
                    v_isShared_3799_ = v_isSharedCheck_3849_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3796_);
                    crate::leanh::lean_inc(v_toSeqLeft_3795_);
                    crate::leanh::lean_inc(v_toSeq_3794_);
                    crate::leanh::lean_inc(v_toFunctor_3793_);
                    crate::leanh::lean_dec(v_toApplicative_3789_);
                    v___x_3798_ = crate::leanh::lean_box(0);
                    v_isShared_3799_ = v_isSharedCheck_3849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3800_ =
                    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1;
                v___f_3801_ =
                    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3793_);
                v___f_3802_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3802_, 0, v_toFunctor_3793_);
                v___f_3803_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3803_, 0, v_toFunctor_3793_);
                v___x_3804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3804_, 0, v___f_3802_);
                crate::leanh::lean_ctor_set(v___x_3804_, 1, v___f_3803_);
                v___f_3805_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3805_, 0, v_toSeqRight_3796_);
                v___f_3806_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3806_, 0, v_toSeqLeft_3795_);
                v___f_3807_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3807_, 0, v_toSeq_3794_);
                if v_isShared_3799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3798_, 4, v___f_3805_);
                    crate::leanh::lean_ctor_set(v___x_3798_, 3, v___f_3806_);
                    crate::leanh::lean_ctor_set(v___x_3798_, 2, v___f_3807_);
                    crate::leanh::lean_ctor_set(v___x_3798_, 1, v___f_3800_);
                    crate::leanh::lean_ctor_set(v___x_3798_, 0, v___x_3804_);
                    v___x_3809_ = v___x_3798_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___f_3800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 2, v___f_3807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 3, v___f_3806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 4, v___f_3805_);
                    v___x_3809_ = v_reuseFailAlloc_3848_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3791_, 1, v___f_3801_);
                    crate::leanh::lean_ctor_set(v___x_3791_, 0, v___x_3809_);
                    v___x_3811_ = v___x_3791_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___f_3801_);
                    v___x_3811_ = v_reuseFailAlloc_3847_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3812_ = l_StateRefT_x27_instMonad___redArg(v___x_3811_);
                v_toApplicative_3813_ = crate::leanh::lean_ctor_get(v___x_3812_, 0);
                v_isSharedCheck_3845_ = (!crate::leanh::lean_is_exclusive(v___x_3812_)) as u8;
                if v_isSharedCheck_3845_ == 0 {
                    v_unused_3846_ = crate::leanh::lean_ctor_get(v___x_3812_, 1);
                    crate::leanh::lean_dec(v_unused_3846_);
                    v___x_3815_ = v___x_3812_;
                    v_isShared_3816_ = v_isSharedCheck_3845_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3813_);
                    crate::leanh::lean_dec(v___x_3812_);
                    v___x_3815_ = crate::leanh::lean_box(0);
                    v_isShared_3816_ = v_isSharedCheck_3845_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3817_ = crate::leanh::lean_ctor_get(v_toApplicative_3813_, 0);
                v_toSeq_3818_ = crate::leanh::lean_ctor_get(v_toApplicative_3813_, 2);
                v_toSeqLeft_3819_ = crate::leanh::lean_ctor_get(v_toApplicative_3813_, 3);
                v_toSeqRight_3820_ = crate::leanh::lean_ctor_get(v_toApplicative_3813_, 4);
                v_isSharedCheck_3843_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3813_)) as u8;
                if v_isSharedCheck_3843_ == 0 {
                    v_unused_3844_ = crate::leanh::lean_ctor_get(v_toApplicative_3813_, 1);
                    crate::leanh::lean_dec(v_unused_3844_);
                    v___x_3822_ = v_toApplicative_3813_;
                    v_isShared_3823_ = v_isSharedCheck_3843_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3820_);
                    crate::leanh::lean_inc(v_toSeqLeft_3819_);
                    crate::leanh::lean_inc(v_toSeq_3818_);
                    crate::leanh::lean_inc(v_toFunctor_3817_);
                    crate::leanh::lean_dec(v_toApplicative_3813_);
                    v___x_3822_ = crate::leanh::lean_box(0);
                    v_isShared_3823_ = v_isSharedCheck_3843_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3824_ =
                    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3;
                v___f_3825_ =
                    l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_3817_);
                v___f_3826_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3826_, 0, v_toFunctor_3817_);
                v___f_3827_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3827_, 0, v_toFunctor_3817_);
                v___x_3828_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3828_, 0, v___f_3826_);
                crate::leanh::lean_ctor_set(v___x_3828_, 1, v___f_3827_);
                v___f_3829_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3829_, 0, v_toSeqRight_3820_);
                v___f_3830_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3830_, 0, v_toSeqLeft_3819_);
                v___f_3831_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3831_, 0, v_toSeq_3818_);
                if v_isShared_3823_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3822_, 4, v___f_3829_);
                    crate::leanh::lean_ctor_set(v___x_3822_, 3, v___f_3830_);
                    crate::leanh::lean_ctor_set(v___x_3822_, 2, v___f_3831_);
                    crate::leanh::lean_ctor_set(v___x_3822_, 1, v___f_3824_);
                    crate::leanh::lean_ctor_set(v___x_3822_, 0, v___x_3828_);
                    v___x_3833_ = v___x_3822_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___f_3824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 2, v___f_3831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 3, v___f_3830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 4, v___f_3829_);
                    v___x_3833_ = v_reuseFailAlloc_3842_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3815_, 1, v___f_3825_);
                    crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3833_);
                    v___x_3835_ = v___x_3815_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___f_3825_);
                    v___x_3835_ = v_reuseFailAlloc_3841_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3836_ = l_StateRefT_x27_instMonad___redArg(v___x_3835_);
                v___x_3837_ = crate::leanh::lean_box(0);
                v___x_3838_ = l_instInhabitedOfMonad___redArg(v___x_3836_, v___x_3837_);
                v___x_4523__overap_3839_ = lean_panic_fn_borrowed(v___x_3838_, v_msg_3780_);
                crate::leanh::lean_dec(v___x_3838_);
                crate::leanh::lean_inc(v___y_3785_);
                crate::leanh::lean_inc_ref(v___y_3784_);
                crate::leanh::lean_inc(v___y_3783_);
                crate::leanh::lean_inc_ref(v___y_3782_);
                crate::leanh::lean_inc(v___y_3781_);
                v___x_3840_ = crate::leanh::lean_apply_6(
                    v___x_4523__overap_3839_,
                    v___y_3781_,
                    v___y_3782_,
                    v___y_3783_,
                    v___y_3784_,
                    v___y_3785_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___boxed(
    mut v_msg_3853_: *mut crate::leanh::LeanObject,
    mut v___y_3854_: *mut crate::leanh::LeanObject,
    mut v___y_3855_: *mut crate::leanh::LeanObject,
    mut v___y_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(
        v_msg_3853_,
        v___y_3854_,
        v___y_3855_,
        v___y_3856_,
        v___y_3857_,
        v___y_3858_,
    );
    crate::leanh::lean_dec(v___y_3858_);
    crate::leanh::lean_dec_ref(v___y_3857_);
    crate::leanh::lean_dec(v___y_3856_);
    crate::leanh::lean_dec_ref(v___y_3855_);
    crate::leanh::lean_dec(v___y_3854_);
    return v_res_3860_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: f64 = 0.0;
    v___x_3861_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3862_ = lean_float_of_nat(v___x_3861_);
    return v___x_3862_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(
    mut v_cls_3866_: *mut crate::leanh::LeanObject,
    mut v_msg_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v_tid_3892_: u64 = 0;
    let mut v_traces_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: f64 = 0.0;
    let mut v___x_3899_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3917_: u8 = 0;
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3873_ = crate::leanh::lean_ctor_get(v___y_3870_, 5);
                v___x_3874_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
                v_a_3875_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                v_isSharedCheck_3919_ = (!crate::leanh::lean_is_exclusive(v___x_3874_)) as u8;
                if v_isSharedCheck_3919_ == 0 {
                    v___x_3877_ = v___x_3874_;
                    v_isShared_3878_ = v_isSharedCheck_3919_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3875_);
                    crate::leanh::lean_dec(v___x_3874_);
                    v___x_3877_ = crate::leanh::lean_box(0);
                    v_isShared_3878_ = v_isSharedCheck_3919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3879_ = lean_st_ref_take(v___y_3871_);
                v_traceState_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 4);
                v_env_3881_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                v_nextMacroScope_3882_ = crate::leanh::lean_ctor_get(v___x_3879_, 1);
                v_ngen_3883_ = crate::leanh::lean_ctor_get(v___x_3879_, 2);
                v_auxDeclNGen_3884_ = crate::leanh::lean_ctor_get(v___x_3879_, 3);
                v_cache_3885_ = crate::leanh::lean_ctor_get(v___x_3879_, 5);
                v_messages_3886_ = crate::leanh::lean_ctor_get(v___x_3879_, 6);
                v_infoState_3887_ = crate::leanh::lean_ctor_get(v___x_3879_, 7);
                v_snapshotTasks_3888_ = crate::leanh::lean_ctor_get(v___x_3879_, 8);
                v_isSharedCheck_3918_ = (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                if v_isSharedCheck_3918_ == 0 {
                    v___x_3890_ = v___x_3879_;
                    v_isShared_3891_ = v_isSharedCheck_3918_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3888_);
                    crate::leanh::lean_inc(v_infoState_3887_);
                    crate::leanh::lean_inc(v_messages_3886_);
                    crate::leanh::lean_inc(v_cache_3885_);
                    crate::leanh::lean_inc(v_traceState_3880_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3884_);
                    crate::leanh::lean_inc(v_ngen_3883_);
                    crate::leanh::lean_inc(v_nextMacroScope_3882_);
                    crate::leanh::lean_inc(v_env_3881_);
                    crate::leanh::lean_dec(v___x_3879_);
                    v___x_3890_ = crate::leanh::lean_box(0);
                    v_isShared_3891_ = v_isSharedCheck_3918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3892_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3880_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3893_ = crate::leanh::lean_ctor_get(v_traceState_3880_, 0);
                v_isSharedCheck_3917_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3880_)) as u8;
                if v_isSharedCheck_3917_ == 0 {
                    v___x_3895_ = v_traceState_3880_;
                    v_isShared_3896_ = v_isSharedCheck_3917_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3893_);
                    crate::leanh::lean_dec(v_traceState_3880_);
                    v___x_3895_ = crate::leanh::lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3897_ = crate::leanh::lean_box(0);
                v___x_3898_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0);
                v___x_3899_ = 0;
                v___x_3900_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1;
                v___x_3901_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3901_, 0, v_cls_3866_);
                crate::leanh::lean_ctor_set(v___x_3901_, 1, v___x_3897_);
                crate::leanh::lean_ctor_set(v___x_3901_, 2, v___x_3900_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3901_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3898_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3901_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3898_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3901_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3899_,
                );
                v___x_3902_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2;
                v___x_3903_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3903_, 0, v___x_3901_);
                crate::leanh::lean_ctor_set(v___x_3903_, 1, v_a_3875_);
                crate::leanh::lean_ctor_set(v___x_3903_, 2, v___x_3902_);
                crate::leanh::lean_inc(v_ref_3873_);
                v___x_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3904_, 0, v_ref_3873_);
                crate::leanh::lean_ctor_set(v___x_3904_, 1, v___x_3903_);
                v___x_3905_ = l_Lean_PersistentArray_push___redArg(v_traces_3893_, v___x_3904_);
                if v_isShared_3896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3895_, 0, v___x_3905_);
                    v___x_3907_ = v___x_3895_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3916_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3905_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3916_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3892_,
                    );
                    v___x_3907_ = v_reuseFailAlloc_3916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3890_, 4, v___x_3907_);
                    v___x_3909_ = v___x_3890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_env_3881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_nextMacroScope_3882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_ngen_3883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 3, v_auxDeclNGen_3884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 4, v___x_3907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 5, v_cache_3885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 6, v_messages_3886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 7, v_infoState_3887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 8, v_snapshotTasks_3888_);
                    v___x_3909_ = v_reuseFailAlloc_3915_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3910_ = lean_st_ref_set(v___y_3871_, v___x_3909_);
                v___x_3911_ = crate::leanh::lean_box(0);
                if v_isShared_3878_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3877_, 0, v___x_3911_);
                    v___x_3913_ = v___x_3877_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
                    v___x_3913_ = v_reuseFailAlloc_3914_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___boxed(
    mut v_cls_3920_: *mut crate::leanh::LeanObject,
    mut v_msg_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
    mut v___y_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
    mut v___y_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3927_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(
        v_cls_3920_,
        v_msg_3921_,
        v___y_3922_,
        v___y_3923_,
        v___y_3924_,
        v___y_3925_,
    );
    crate::leanh::lean_dec(v___y_3925_);
    crate::leanh::lean_dec_ref(v___y_3924_);
    crate::leanh::lean_dec(v___y_3923_);
    crate::leanh::lean_dec_ref(v___y_3922_);
    return v_res_3927_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3937_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2;
    v___x_3938_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4;
    v___x_3939_ = l_Lean_Name_append(v___x_3938_, v___x_3937_);
    return v___x_3939_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6;
    v___x_3942_ = l_Lean_stringToMessageData(v___x_3941_);
    return v___x_3942_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8;
    v___x_3945_ = l_Lean_stringToMessageData(v___x_3944_);
    return v___x_3945_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10;
    v___x_3948_ = l_Lean_stringToMessageData(v___x_3947_);
    return v___x_3948_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14;
    v___x_3953_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_3954_ = crate::leanh::lean_unsigned_to_nat(309);
    v___x_3955_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13;
    v___x_3956_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12;
    v___x_3957_ = l_mkPanicMessageWithDecl(
        v___x_3956_,
        v___x_3955_,
        v___x_3954_,
        v___x_3953_,
        v___x_3952_,
    );
    return v___x_3957_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_lookup(
    mut v_e_3958_: *mut crate::leanh::LeanObject,
    mut v_width_3959_: *mut crate::leanh::LeanObject,
    mut v_synthetic_3960_: u8,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atoms_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v_size_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v_unused_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atoms_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3991_: u8 = 0;
    let mut v_inheritedTraceOptions_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v_width_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomNumber_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4043_: u8 = 0;
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4047_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3987_ = lean_st_ref_get(v_a_3961_);
                v_atoms_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                crate::leanh::lean_inc_ref(v_atoms_3988_);
                crate::leanh::lean_dec(v___x_3987_);
                v___x_3989_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_3988_, v_e_3958_);
                crate::leanh::lean_dec_ref(v_atoms_3988_);
                if crate::leanh::lean_obj_tag(v___x_3989_) == 0 {
                    v_options_3990_ = crate::leanh::lean_ctor_get(v_a_3964_, 2);
                    v_hasTrace_3991_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3990_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3991_ == 0 {
                        v___y_3968_ = v_a_3961_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3992_ = crate::leanh::lean_ctor_get(v_a_3964_, 13);
                        v___x_3993_ = l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2;
                        v___x_3994_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5,
                        );
                        v___x_3995_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3992_,
                            v_options_3990_,
                            v___x_3994_,
                        );
                        if v___x_3995_ == 0 {
                            v___y_3968_ = v_a_3961_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3996_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7_once
                                ),
                                _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7,
                            );
                            crate::leanh::lean_inc(v_width_3959_);
                            v___x_3997_ = l_Nat_reprFast(v_width_3959_);
                            v___x_3998_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3998_, 0, v___x_3997_);
                            v___x_3999_ = l_Lean_MessageData_ofFormat(v___x_3998_);
                            v___x_4000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_3996_);
                            crate::leanh::lean_ctor_set(v___x_4000_, 1, v___x_3999_);
                            v___x_4001_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9_once
                                ),
                                _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9,
                            );
                            v___x_4002_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4002_, 0, v___x_4000_);
                            crate::leanh::lean_ctor_set(v___x_4002_, 1, v___x_4001_);
                            if v_synthetic_3960_ == 0 {
                                v___x_4021_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7;
                                v___y_4004_ = v___x_4021_;
                                state = 4;
                                continue;
                            } else {
                                v___x_4022_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10;
                                v___y_4004_ = v___x_4022_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3958_);
                    v_val_4023_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                    v_isSharedCheck_4051_ = (!crate::leanh::lean_is_exclusive(v___x_3989_)) as u8;
                    if v_isSharedCheck_4051_ == 0 {
                        v___x_4025_ = v___x_3989_;
                        v_isShared_4026_ = v_isSharedCheck_4051_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4023_);
                        crate::leanh::lean_dec(v___x_3989_);
                        v___x_4025_ = crate::leanh::lean_box(0);
                        v_isShared_4026_ = v_isSharedCheck_4051_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3969_ = lean_st_ref_take(v___y_3968_);
                v_atoms_3970_ = crate::leanh::lean_ctor_get(v___x_3969_, 0);
                v_isSharedCheck_3984_ = (!crate::leanh::lean_is_exclusive(v___x_3969_)) as u8;
                if v_isSharedCheck_3984_ == 0 {
                    v_unused_3985_ = crate::leanh::lean_ctor_get(v___x_3969_, 2);
                    crate::leanh::lean_dec(v_unused_3985_);
                    v_unused_3986_ = crate::leanh::lean_ctor_get(v___x_3969_, 1);
                    crate::leanh::lean_dec(v_unused_3986_);
                    v___x_3972_ = v___x_3969_;
                    v_isShared_3973_ = v_isSharedCheck_3984_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_atoms_3970_);
                    crate::leanh::lean_dec(v___x_3969_);
                    v___x_3972_ = crate::leanh::lean_box(0);
                    v_isShared_3973_ = v_isSharedCheck_3984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_size_3974_ = crate::leanh::lean_ctor_get(v_atoms_3970_, 0);
                crate::leanh::lean_inc_n(v_size_3974_, 2);
                v___x_3975_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3975_, 0, v_width_3959_);
                crate::leanh::lean_ctor_set(v___x_3975_, 1, v_size_3974_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3975_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_synthetic_3960_,
                );
                v___x_3976_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_atoms_3970_, v_e_3958_, v___x_3975_);
                v___x_3977_ = crate::leanh::lean_box(0);
                v___x_3978_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1,
                );
                if v_isShared_3973_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3972_, 2, v___x_3978_);
                    crate::leanh::lean_ctor_set(v___x_3972_, 1, v___x_3977_);
                    crate::leanh::lean_ctor_set(v___x_3972_, 0, v___x_3976_);
                    v___x_3980_ = v___x_3972_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 2, v___x_3978_);
                    v___x_3980_ = v_reuseFailAlloc_3983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3981_ = lean_st_ref_set(v___y_3968_, v___x_3980_);
                v___x_3982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3982_, 0, v_size_3974_);
                return v___x_3982_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_4004_);
                v___x_4005_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4005_, 0, v___y_4004_);
                v___x_4006_ = l_Lean_MessageData_ofFormat(v___x_4005_);
                v___x_4007_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_4002_);
                crate::leanh::lean_ctor_set(v___x_4007_, 1, v___x_4006_);
                v___x_4008_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11_once),
                    _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11,
                );
                v___x_4009_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4009_, 0, v___x_4007_);
                crate::leanh::lean_ctor_set(v___x_4009_, 1, v___x_4008_);
                crate::leanh::lean_inc_ref(v_e_3958_);
                v___x_4010_ = l_Lean_MessageData_ofExpr(v_e_3958_);
                v___x_4011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4011_, 0, v___x_4009_);
                crate::leanh::lean_ctor_set(v___x_4011_, 1, v___x_4010_);
                v___x_4012_ =
                    l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(
                        v___x_3993_,
                        v___x_4011_,
                        v_a_3962_,
                        v_a_3963_,
                        v_a_3964_,
                        v_a_3965_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4012_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4012_, 1);
                    v___y_3968_ = v_a_3961_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_width_3959_);
                    crate::leanh::lean_dec_ref(v_e_3958_);
                    v_a_4013_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                    v_isSharedCheck_4020_ = (!crate::leanh::lean_is_exclusive(v___x_4012_)) as u8;
                    if v_isSharedCheck_4020_ == 0 {
                        v___x_4015_ = v___x_4012_;
                        v_isShared_4016_ = v_isSharedCheck_4020_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4013_);
                        crate::leanh::lean_dec(v___x_4012_);
                        v___x_4015_ = crate::leanh::lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4020_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4016_ == 0 {
                    v___x_4018_ = v___x_4015_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4018_;
            }
            7 => {
                v_width_4027_ = crate::leanh::lean_ctor_get(v_val_4023_, 0);
                crate::leanh::lean_inc(v_width_4027_);
                v_atomNumber_4028_ = crate::leanh::lean_ctor_get(v_val_4023_, 1);
                crate::leanh::lean_inc(v_atomNumber_4028_);
                crate::leanh::lean_dec(v_val_4023_);
                v___x_4029_ = lean_nat_dec_eq(v_width_3959_, v_width_4027_);
                crate::leanh::lean_dec(v_width_4027_);
                crate::leanh::lean_dec(v_width_3959_);
                if v___x_4029_ == 0 {
                    crate::leanh::lean_del_object(v___x_4025_);
                    v___x_4030_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15,
                    );
                    v___x_4031_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(
                        v___x_4030_,
                        v_a_3961_,
                        v_a_3962_,
                        v_a_3963_,
                        v_a_3964_,
                        v_a_3965_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4031_) == 0 {
                        v_isSharedCheck_4038_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4031_)) as u8;
                        if v_isSharedCheck_4038_ == 0 {
                            v_unused_4039_ = crate::leanh::lean_ctor_get(v___x_4031_, 0);
                            crate::leanh::lean_dec(v_unused_4039_);
                            v___x_4033_ = v___x_4031_;
                            v_isShared_4034_ = v_isSharedCheck_4038_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4031_);
                            v___x_4033_ = crate::leanh::lean_box(0);
                            v_isShared_4034_ = v_isSharedCheck_4038_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_atomNumber_4028_);
                        v_a_4040_ = crate::leanh::lean_ctor_get(v___x_4031_, 0);
                        v_isSharedCheck_4047_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4031_)) as u8;
                        if v_isSharedCheck_4047_ == 0 {
                            v___x_4042_ = v___x_4031_;
                            v_isShared_4043_ = v_isSharedCheck_4047_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4040_);
                            crate::leanh::lean_dec(v___x_4031_);
                            v___x_4042_ = crate::leanh::lean_box(0);
                            v_isShared_4043_ = v_isSharedCheck_4047_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_4026_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4025_, 0);
                        crate::leanh::lean_ctor_set(v___x_4025_, 0, v_atomNumber_4028_);
                        v___x_4049_ = v___x_4025_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4050_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_atomNumber_4028_);
                        v___x_4049_ = v_reuseFailAlloc_4050_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4033_, 0, v_atomNumber_4028_);
                    v___x_4036_ = v___x_4033_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_atomNumber_4028_);
                    v___x_4036_ = v_reuseFailAlloc_4037_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4036_;
            }
            10 => {
                if v_isShared_4043_ == 0 {
                    v___x_4045_ = v___x_4042_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
                    v___x_4045_ = v_reuseFailAlloc_4046_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4045_;
            }
            12 => {
                return v___x_4049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_lookup___boxed(
    mut v_e_4052_: *mut crate::leanh::LeanObject,
    mut v_width_4053_: *mut crate::leanh::LeanObject,
    mut v_synthetic_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
    mut v_a_4059_: *mut crate::leanh::LeanObject,
    mut v_a_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthetic_boxed_4061_: u8 = 0;
    let mut v_res_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_4061_ = (crate::leanh::lean_unbox(v_synthetic_4054_) as u8);
    v_res_4062_ = l_Lean_Meta_Tactic_BVDecide_M_lookup(
        v_e_4052_,
        v_width_4053_,
        v_synthetic_boxed_4061_,
        v_a_4055_,
        v_a_4056_,
        v_a_4057_,
        v_a_4058_,
        v_a_4059_,
    );
    crate::leanh::lean_dec(v_a_4059_);
    crate::leanh::lean_dec_ref(v_a_4058_);
    crate::leanh::lean_dec(v_a_4057_);
    crate::leanh::lean_dec_ref(v_a_4056_);
    crate::leanh::lean_dec(v_a_4055_);
    return v_res_4062_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0(
    mut v_cls_4063_: *mut crate::leanh::LeanObject,
    mut v_msg_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(
        v_cls_4063_,
        v_msg_4064_,
        v___y_4066_,
        v___y_4067_,
        v___y_4068_,
        v___y_4069_,
    );
    return v___x_4071_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___boxed(
    mut v_cls_4072_: *mut crate::leanh::LeanObject,
    mut v_msg_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0(
        v_cls_4072_,
        v_msg_4073_,
        v___y_4074_,
        v___y_4075_,
        v___y_4076_,
        v___y_4077_,
        v___y_4078_,
    );
    crate::leanh::lean_dec(v___y_4078_);
    crate::leanh::lean_dec_ref(v___y_4077_);
    crate::leanh::lean_dec(v___y_4076_);
    crate::leanh::lean_dec_ref(v___y_4075_);
    crate::leanh::lean_dec(v___y_4074_);
    return v_res_4080_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(
    mut v_mkFRefl_4081_: *mut crate::leanh::LeanObject,
    mut v_fst_4082_: *mut crate::leanh::LeanObject,
    mut v_fproof_4083_: *mut crate::leanh::LeanObject,
    mut v_mkSRefl_4084_: *mut crate::leanh::LeanObject,
    mut v_snd_4085_: *mut crate::leanh::LeanObject,
    mut v_sproof_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_val_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4107_: u8 = 0;
    let mut v_val_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fproof_4083_) == 0 {
                    crate::leanh::lean_dec_ref(v_snd_4085_);
                    crate::leanh::lean_dec_ref(v_mkSRefl_4084_);
                    if crate::leanh::lean_obj_tag(v_sproof_4086_) == 0 {
                        crate::leanh::lean_dec_ref(v_fst_4082_);
                        crate::leanh::lean_dec_ref(v_mkFRefl_4081_);
                        v___x_4087_ = crate::leanh::lean_box(0);
                        return v___x_4087_;
                    } else {
                        v_val_4088_ = crate::leanh::lean_ctor_get(v_sproof_4086_, 0);
                        v_isSharedCheck_4097_ =
                            (!crate::leanh::lean_is_exclusive(v_sproof_4086_)) as u8;
                        if v_isSharedCheck_4097_ == 0 {
                            v___x_4090_ = v_sproof_4086_;
                            v_isShared_4091_ = v_isSharedCheck_4097_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4088_);
                            crate::leanh::lean_dec(v_sproof_4086_);
                            v___x_4090_ = crate::leanh::lean_box(0);
                            v_isShared_4091_ = v_isSharedCheck_4097_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fst_4082_);
                    crate::leanh::lean_dec_ref(v_mkFRefl_4081_);
                    if crate::leanh::lean_obj_tag(v_sproof_4086_) == 0 {
                        v_val_4098_ = crate::leanh::lean_ctor_get(v_fproof_4083_, 0);
                        v_isSharedCheck_4107_ =
                            (!crate::leanh::lean_is_exclusive(v_fproof_4083_)) as u8;
                        if v_isSharedCheck_4107_ == 0 {
                            v___x_4100_ = v_fproof_4083_;
                            v_isShared_4101_ = v_isSharedCheck_4107_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4098_);
                            crate::leanh::lean_dec(v_fproof_4083_);
                            v___x_4100_ = crate::leanh::lean_box(0);
                            v_isShared_4101_ = v_isSharedCheck_4107_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_snd_4085_);
                        crate::leanh::lean_dec_ref(v_mkSRefl_4084_);
                        v_val_4108_ = crate::leanh::lean_ctor_get(v_fproof_4083_, 0);
                        crate::leanh::lean_inc(v_val_4108_);
                        crate::leanh::lean_dec_ref_known(v_fproof_4083_, 1);
                        v_val_4109_ = crate::leanh::lean_ctor_get(v_sproof_4086_, 0);
                        v_isSharedCheck_4117_ =
                            (!crate::leanh::lean_is_exclusive(v_sproof_4086_)) as u8;
                        if v_isSharedCheck_4117_ == 0 {
                            v___x_4111_ = v_sproof_4086_;
                            v_isShared_4112_ = v_isSharedCheck_4117_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4109_);
                            crate::leanh::lean_dec(v_sproof_4086_);
                            v___x_4111_ = crate::leanh::lean_box(0);
                            v_isShared_4112_ = v_isSharedCheck_4117_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4092_ = crate::leanh::lean_apply_1(v_mkFRefl_4081_, v_fst_4082_);
                v___x_4093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
                crate::leanh::lean_ctor_set(v___x_4093_, 1, v_val_4088_);
                if v_isShared_4091_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4090_, 0, v___x_4093_);
                    v___x_4095_ = v___x_4090_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4095_;
            }
            3 => {
                v___x_4102_ = crate::leanh::lean_apply_1(v_mkSRefl_4084_, v_snd_4085_);
                v___x_4103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4103_, 0, v_val_4098_);
                crate::leanh::lean_ctor_set(v___x_4103_, 1, v___x_4102_);
                if v_isShared_4101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4100_, 0, v___x_4103_);
                    v___x_4105_ = v___x_4100_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
                    v___x_4105_ = v_reuseFailAlloc_4106_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4105_;
            }
            5 => {
                v___x_4113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4113_, 0, v_val_4108_);
                crate::leanh::lean_ctor_set(v___x_4113_, 1, v_val_4109_);
                if v_isShared_4112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4113_);
                    v___x_4115_ = v___x_4111_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
                    v___x_4115_ = v_reuseFailAlloc_4116_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof(
    mut v_mkRefl_4118_: *mut crate::leanh::LeanObject,
    mut v_fst_4119_: *mut crate::leanh::LeanObject,
    mut v_fproof_4120_: *mut crate::leanh::LeanObject,
    mut v_snd_4121_: *mut crate::leanh::LeanObject,
    mut v_sproof_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_mkRefl_4118_);
    v___x_4123_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(
        v_mkRefl_4118_,
        v_fst_4119_,
        v_fproof_4120_,
        v_mkRefl_4118_,
        v_snd_4121_,
        v_sproof_4122_,
    );
    return v___x_4123_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof(
    mut v_mkRefl_4124_: *mut crate::leanh::LeanObject,
    mut v_fst_4125_: *mut crate::leanh::LeanObject,
    mut v_fproof_4126_: *mut crate::leanh::LeanObject,
    mut v_snd_4127_: *mut crate::leanh::LeanObject,
    mut v_sproof_4128_: *mut crate::leanh::LeanObject,
    mut v_thd_4129_: *mut crate::leanh::LeanObject,
    mut v_tproof_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4142_: u8 = 0;
    let mut v_val_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4158_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4163_: u8 = 0;
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fproof_4126_) == 0 {
                    crate::leanh::lean_inc_ref_n(v_mkRefl_4124_, 2);
                    v___x_4131_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(
                        v_mkRefl_4124_,
                        v_snd_4127_,
                        v_sproof_4128_,
                        v_mkRefl_4124_,
                        v_thd_4129_,
                        v_tproof_4130_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4131_) == 0 {
                        crate::leanh::lean_dec_ref(v_fst_4125_);
                        crate::leanh::lean_dec_ref(v_mkRefl_4124_);
                        v___x_4132_ = crate::leanh::lean_box(0);
                        return v___x_4132_;
                    } else {
                        v_val_4133_ = crate::leanh::lean_ctor_get(v___x_4131_, 0);
                        v_isSharedCheck_4142_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4131_)) as u8;
                        if v_isSharedCheck_4142_ == 0 {
                            v___x_4135_ = v___x_4131_;
                            v_isShared_4136_ = v_isSharedCheck_4142_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4133_);
                            crate::leanh::lean_dec(v___x_4131_);
                            v___x_4135_ = crate::leanh::lean_box(0);
                            v_isShared_4136_ = v_isSharedCheck_4142_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fst_4125_);
                    v_val_4143_ = crate::leanh::lean_ctor_get(v_fproof_4126_, 0);
                    v_isSharedCheck_4164_ =
                        (!crate::leanh::lean_is_exclusive(v_fproof_4126_)) as u8;
                    if v_isSharedCheck_4164_ == 0 {
                        v___x_4145_ = v_fproof_4126_;
                        v_isShared_4146_ = v_isSharedCheck_4164_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4143_);
                        crate::leanh::lean_dec(v_fproof_4126_);
                        v___x_4145_ = crate::leanh::lean_box(0);
                        v_isShared_4146_ = v_isSharedCheck_4164_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4137_ = crate::leanh::lean_apply_1(v_mkRefl_4124_, v_fst_4125_);
                v___x_4138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4137_);
                crate::leanh::lean_ctor_set(v___x_4138_, 1, v_val_4133_);
                if v_isShared_4136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4138_);
                    v___x_4140_ = v___x_4135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4138_);
                    v___x_4140_ = v_reuseFailAlloc_4141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4140_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_thd_4129_);
                crate::leanh::lean_inc_ref(v_snd_4127_);
                crate::leanh::lean_inc_ref_n(v_mkRefl_4124_, 2);
                v___x_4147_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(
                    v_mkRefl_4124_,
                    v_snd_4127_,
                    v_sproof_4128_,
                    v_mkRefl_4124_,
                    v_thd_4129_,
                    v_tproof_4130_,
                );
                if crate::leanh::lean_obj_tag(v___x_4147_) == 0 {
                    crate::leanh::lean_inc_ref(v_mkRefl_4124_);
                    v___x_4148_ = crate::leanh::lean_apply_1(v_mkRefl_4124_, v_snd_4127_);
                    v___x_4149_ = crate::leanh::lean_apply_1(v_mkRefl_4124_, v_thd_4129_);
                    v___x_4150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4150_, 0, v___x_4148_);
                    crate::leanh::lean_ctor_set(v___x_4150_, 1, v___x_4149_);
                    v___x_4151_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v_val_4143_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v___x_4150_);
                    if v_isShared_4146_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4145_, 0, v___x_4151_);
                        v___x_4153_ = v___x_4145_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
                        v___x_4153_ = v_reuseFailAlloc_4154_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4145_);
                    crate::leanh::lean_dec_ref(v_thd_4129_);
                    crate::leanh::lean_dec_ref(v_snd_4127_);
                    crate::leanh::lean_dec_ref(v_mkRefl_4124_);
                    v_val_4155_ = crate::leanh::lean_ctor_get(v___x_4147_, 0);
                    v_isSharedCheck_4163_ = (!crate::leanh::lean_is_exclusive(v___x_4147_)) as u8;
                    if v_isSharedCheck_4163_ == 0 {
                        v___x_4157_ = v___x_4147_;
                        v_isShared_4158_ = v_isSharedCheck_4163_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4155_);
                        crate::leanh::lean_dec(v___x_4147_);
                        v___x_4157_ = crate::leanh::lean_box(0);
                        v_isShared_4158_ = v_isSharedCheck_4163_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4153_;
            }
            5 => {
                v___x_4159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4159_, 0, v_val_4143_);
                crate::leanh::lean_ctor_set(v___x_4159_, 1, v_val_4155_);
                if v_isShared_4158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4157_, 0, v___x_4159_);
                    v___x_4161_ = v___x_4157_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
                    v___x_4161_ = v_reuseFailAlloc_4162_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(
    mut v_m_4165_: *mut crate::leanh::LeanObject,
    mut v_state_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
    mut v_a_4169_: *mut crate::leanh::LeanObject,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_a_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4173_ = lean_st_mk_ref(v_state_4166_);
                crate::leanh::lean_inc(v_a_4171_);
                crate::leanh::lean_inc_ref(v_a_4170_);
                crate::leanh::lean_inc(v_a_4169_);
                crate::leanh::lean_inc_ref(v_a_4168_);
                crate::leanh::lean_inc(v_a_4167_);
                crate::leanh::lean_inc(v___x_4173_);
                v___x_4174_ = crate::leanh::lean_apply_7(
                    v_m_4165_,
                    v___x_4173_,
                    v_a_4167_,
                    v_a_4168_,
                    v_a_4169_,
                    v_a_4170_,
                    v_a_4171_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4174_) == 0 {
                    v_a_4175_ = crate::leanh::lean_ctor_get(v___x_4174_, 0);
                    v_isSharedCheck_4185_ = (!crate::leanh::lean_is_exclusive(v___x_4174_)) as u8;
                    if v_isSharedCheck_4185_ == 0 {
                        v___x_4177_ = v___x_4174_;
                        v_isShared_4178_ = v_isSharedCheck_4185_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4175_);
                        crate::leanh::lean_dec(v___x_4174_);
                        v___x_4177_ = crate::leanh::lean_box(0);
                        v_isShared_4178_ = v_isSharedCheck_4185_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4173_);
                    v_a_4186_ = crate::leanh::lean_ctor_get(v___x_4174_, 0);
                    v_isSharedCheck_4193_ = (!crate::leanh::lean_is_exclusive(v___x_4174_)) as u8;
                    if v_isSharedCheck_4193_ == 0 {
                        v___x_4188_ = v___x_4174_;
                        v_isShared_4189_ = v_isSharedCheck_4193_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4186_);
                        crate::leanh::lean_dec(v___x_4174_);
                        v___x_4188_ = crate::leanh::lean_box(0);
                        v_isShared_4189_ = v_isSharedCheck_4193_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4179_ = lean_st_ref_get(v___x_4173_);
                crate::leanh::lean_dec(v___x_4173_);
                v_lemmas_4180_ = crate::leanh::lean_ctor_get(v___x_4179_, 0);
                crate::leanh::lean_inc_ref(v_lemmas_4180_);
                crate::leanh::lean_dec(v___x_4179_);
                v___x_4181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4181_, 0, v_a_4175_);
                crate::leanh::lean_ctor_set(v___x_4181_, 1, v_lemmas_4180_);
                if v_isShared_4178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4177_, 0, v___x_4181_);
                    v___x_4183_ = v___x_4177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
                    v___x_4183_ = v_reuseFailAlloc_4184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4183_;
            }
            3 => {
                if v_isShared_4189_ == 0 {
                    v___x_4191_ = v___x_4188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
                    v___x_4191_ = v_reuseFailAlloc_4192_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg___boxed(
    mut v_m_4194_: *mut crate::leanh::LeanObject,
    mut v_state_4195_: *mut crate::leanh::LeanObject,
    mut v_a_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(
        v_m_4194_,
        v_state_4195_,
        v_a_4196_,
        v_a_4197_,
        v_a_4198_,
        v_a_4199_,
        v_a_4200_,
    );
    crate::leanh::lean_dec(v_a_4200_);
    crate::leanh::lean_dec_ref(v_a_4199_);
    crate::leanh::lean_dec(v_a_4198_);
    crate::leanh::lean_dec_ref(v_a_4197_);
    crate::leanh::lean_dec(v_a_4196_);
    return v_res_4202_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_run(
    mut v_00_u03b1_4203_: *mut crate::leanh::LeanObject,
    mut v_m_4204_: *mut crate::leanh::LeanObject,
    mut v_state_4205_: *mut crate::leanh::LeanObject,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4212_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(
        v_m_4204_,
        v_state_4205_,
        v_a_4206_,
        v_a_4207_,
        v_a_4208_,
        v_a_4209_,
        v_a_4210_,
    );
    return v___x_4212_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(
    mut v_00_u03b1_4213_: *mut crate::leanh::LeanObject,
    mut v_m_4214_: *mut crate::leanh::LeanObject,
    mut v_state_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4222_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run(
        v_00_u03b1_4213_,
        v_m_4214_,
        v_state_4215_,
        v_a_4216_,
        v_a_4217_,
        v_a_4218_,
        v_a_4219_,
        v_a_4220_,
    );
    crate::leanh::lean_dec(v_a_4220_);
    crate::leanh::lean_dec_ref(v_a_4219_);
    crate::leanh::lean_dec(v_a_4218_);
    crate::leanh::lean_dec_ref(v_a_4217_);
    crate::leanh::lean_dec(v_a_4216_);
    return v_res_4222_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(
    mut v_lemma_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4226_ = lean_st_ref_take(v_a_4224_);
                v_lemmas_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                v_bvExprCache_4228_ = crate::leanh::lean_ctor_get(v___x_4226_, 1);
                v_bvPredCache_4229_ = crate::leanh::lean_ctor_get(v___x_4226_, 2);
                v_bvLogicalCache_4230_ = crate::leanh::lean_ctor_get(v___x_4226_, 3);
                v_isSharedCheck_4241_ = (!crate::leanh::lean_is_exclusive(v___x_4226_)) as u8;
                if v_isSharedCheck_4241_ == 0 {
                    v___x_4232_ = v___x_4226_;
                    v_isShared_4233_ = v_isSharedCheck_4241_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_4230_);
                    crate::leanh::lean_inc(v_bvPredCache_4229_);
                    crate::leanh::lean_inc(v_bvExprCache_4228_);
                    crate::leanh::lean_inc(v_lemmas_4227_);
                    crate::leanh::lean_dec(v___x_4226_);
                    v___x_4232_ = crate::leanh::lean_box(0);
                    v_isShared_4233_ = v_isSharedCheck_4241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4234_ = lean_array_push(v_lemmas_4227_, v_lemma_4223_);
                if v_isShared_4233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4232_, 0, v___x_4234_);
                    v___x_4236_ = v___x_4232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_bvExprCache_4228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 2, v_bvPredCache_4229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 3, v_bvLogicalCache_4230_);
                    v___x_4236_ = v_reuseFailAlloc_4240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4237_ = lean_st_ref_set(v_a_4224_, v___x_4236_);
                v___x_4238_ = crate::leanh::lean_box(0);
                v___x_4239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4239_, 0, v___x_4238_);
                return v___x_4239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg___boxed(
    mut v_lemma_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4245_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_4242_, v_a_4243_);
    crate::leanh::lean_dec(v_a_4243_);
    return v_res_4245_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(
    mut v_lemma_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4254_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_4246_, v_a_4247_);
    return v___x_4254_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___boxed(
    mut v_lemma_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
    mut v_a_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4263_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(
        v_lemma_4255_,
        v_a_4256_,
        v_a_4257_,
        v_a_4258_,
        v_a_4259_,
        v_a_4260_,
        v_a_4261_,
    );
    crate::leanh::lean_dec(v_a_4261_);
    crate::leanh::lean_dec_ref(v_a_4260_);
    crate::leanh::lean_dec(v_a_4259_);
    crate::leanh::lean_dec_ref(v_a_4258_);
    crate::leanh::lean_dec(v_a_4257_);
    crate::leanh::lean_dec(v_a_4256_);
    return v_res_4263_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(
    mut v_e_4266_: *mut crate::leanh::LeanObject,
    mut v_f_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_val_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4275_ = lean_st_ref_get(v_a_4268_);
                v_bvExprCache_4276_ = crate::leanh::lean_ctor_get(v___x_4275_, 1);
                crate::leanh::lean_inc_ref(v_bvExprCache_4276_);
                crate::leanh::lean_dec(v___x_4275_);
                v___x_4277_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0;
                v___x_4278_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1;
                crate::leanh::lean_inc_ref(v_e_4266_);
                v___x_4279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___x_4277_,
                    v___x_4278_,
                    v_bvExprCache_4276_,
                    v_e_4266_,
                );
                crate::leanh::lean_dec_ref(v_bvExprCache_4276_);
                if crate::leanh::lean_obj_tag(v___x_4279_) == 0 {
                    crate::leanh::lean_inc(v_a_4273_);
                    crate::leanh::lean_inc_ref(v_a_4272_);
                    crate::leanh::lean_inc(v_a_4271_);
                    crate::leanh::lean_inc_ref(v_a_4270_);
                    crate::leanh::lean_inc(v_a_4269_);
                    crate::leanh::lean_inc(v_a_4268_);
                    crate::leanh::lean_inc_ref(v_e_4266_);
                    v___x_4280_ = crate::leanh::lean_apply_8(
                        v_f_4267_,
                        v_e_4266_,
                        v_a_4268_,
                        v_a_4269_,
                        v_a_4270_,
                        v_a_4271_,
                        v_a_4272_,
                        v_a_4273_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4280_) == 0 {
                        v_a_4281_ = crate::leanh::lean_ctor_get(v___x_4280_, 0);
                        v_isSharedCheck_4302_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4280_)) as u8;
                        if v_isSharedCheck_4302_ == 0 {
                            v___x_4283_ = v___x_4280_;
                            v_isShared_4284_ = v_isSharedCheck_4302_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4281_);
                            crate::leanh::lean_dec(v___x_4280_);
                            v___x_4283_ = crate::leanh::lean_box(0);
                            v_isShared_4284_ = v_isSharedCheck_4302_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4266_);
                        return v___x_4280_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4267_);
                    crate::leanh::lean_dec_ref(v_e_4266_);
                    v_val_4303_ = crate::leanh::lean_ctor_get(v___x_4279_, 0);
                    v_isSharedCheck_4310_ = (!crate::leanh::lean_is_exclusive(v___x_4279_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4305_ = v___x_4279_;
                        v_isShared_4306_ = v_isSharedCheck_4310_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4303_);
                        crate::leanh::lean_dec(v___x_4279_);
                        v___x_4305_ = crate::leanh::lean_box(0);
                        v_isShared_4306_ = v_isSharedCheck_4310_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4285_ = lean_st_ref_take(v_a_4268_);
                v_lemmas_4286_ = crate::leanh::lean_ctor_get(v___x_4285_, 0);
                v_bvExprCache_4287_ = crate::leanh::lean_ctor_get(v___x_4285_, 1);
                v_bvPredCache_4288_ = crate::leanh::lean_ctor_get(v___x_4285_, 2);
                v_bvLogicalCache_4289_ = crate::leanh::lean_ctor_get(v___x_4285_, 3);
                v_isSharedCheck_4301_ = (!crate::leanh::lean_is_exclusive(v___x_4285_)) as u8;
                if v_isSharedCheck_4301_ == 0 {
                    v___x_4291_ = v___x_4285_;
                    v_isShared_4292_ = v_isSharedCheck_4301_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_4289_);
                    crate::leanh::lean_inc(v_bvPredCache_4288_);
                    crate::leanh::lean_inc(v_bvExprCache_4287_);
                    crate::leanh::lean_inc(v_lemmas_4286_);
                    crate::leanh::lean_dec(v___x_4285_);
                    v___x_4291_ = crate::leanh::lean_box(0);
                    v_isShared_4292_ = v_isSharedCheck_4301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_4281_);
                v___x_4293_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4277_,
                    v___x_4278_,
                    v_bvExprCache_4287_,
                    v_e_4266_,
                    v_a_4281_,
                );
                if v_isShared_4292_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4291_, 1, v___x_4293_);
                    v___x_4295_ = v___x_4291_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_lemmas_4286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 1, v___x_4293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 2, v_bvPredCache_4288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 3, v_bvLogicalCache_4289_);
                    v___x_4295_ = v_reuseFailAlloc_4300_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4296_ = lean_st_ref_set(v_a_4268_, v___x_4295_);
                if v_isShared_4284_ == 0 {
                    v___x_4298_ = v___x_4283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4281_);
                    v___x_4298_ = v_reuseFailAlloc_4299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4298_;
            }
            5 => {
                if v_isShared_4306_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4305_, 0);
                    v___x_4308_ = v___x_4305_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_val_4303_);
                    v___x_4308_ = v_reuseFailAlloc_4309_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___boxed(
    mut v_e_4311_: *mut crate::leanh::LeanObject,
    mut v_f_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4320_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(
        v_e_4311_, v_f_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_,
    );
    crate::leanh::lean_dec(v_a_4318_);
    crate::leanh::lean_dec_ref(v_a_4317_);
    crate::leanh::lean_dec(v_a_4316_);
    crate::leanh::lean_dec_ref(v_a_4315_);
    crate::leanh::lean_dec(v_a_4314_);
    crate::leanh::lean_dec(v_a_4313_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(
    mut v_e_4321_: *mut crate::leanh::LeanObject,
    mut v_f_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
    mut v_a_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4339_: u8 = 0;
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v_isSharedCheck_4357_: u8 = 0;
    let mut v_val_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4330_ = lean_st_ref_get(v_a_4323_);
                v_bvPredCache_4331_ = crate::leanh::lean_ctor_get(v___x_4330_, 2);
                crate::leanh::lean_inc_ref(v_bvPredCache_4331_);
                crate::leanh::lean_dec(v___x_4330_);
                v___x_4332_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0;
                v___x_4333_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1;
                crate::leanh::lean_inc_ref(v_e_4321_);
                v___x_4334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___x_4332_,
                    v___x_4333_,
                    v_bvPredCache_4331_,
                    v_e_4321_,
                );
                crate::leanh::lean_dec_ref(v_bvPredCache_4331_);
                if crate::leanh::lean_obj_tag(v___x_4334_) == 0 {
                    crate::leanh::lean_inc(v_a_4328_);
                    crate::leanh::lean_inc_ref(v_a_4327_);
                    crate::leanh::lean_inc(v_a_4326_);
                    crate::leanh::lean_inc_ref(v_a_4325_);
                    crate::leanh::lean_inc(v_a_4324_);
                    crate::leanh::lean_inc(v_a_4323_);
                    crate::leanh::lean_inc_ref(v_e_4321_);
                    v___x_4335_ = crate::leanh::lean_apply_8(
                        v_f_4322_,
                        v_e_4321_,
                        v_a_4323_,
                        v_a_4324_,
                        v_a_4325_,
                        v_a_4326_,
                        v_a_4327_,
                        v_a_4328_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4335_) == 0 {
                        v_a_4336_ = crate::leanh::lean_ctor_get(v___x_4335_, 0);
                        v_isSharedCheck_4357_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4335_)) as u8;
                        if v_isSharedCheck_4357_ == 0 {
                            v___x_4338_ = v___x_4335_;
                            v_isShared_4339_ = v_isSharedCheck_4357_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4336_);
                            crate::leanh::lean_dec(v___x_4335_);
                            v___x_4338_ = crate::leanh::lean_box(0);
                            v_isShared_4339_ = v_isSharedCheck_4357_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4321_);
                        return v___x_4335_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4322_);
                    crate::leanh::lean_dec_ref(v_e_4321_);
                    v_val_4358_ = crate::leanh::lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4365_ = (!crate::leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4365_ == 0 {
                        v___x_4360_ = v___x_4334_;
                        v_isShared_4361_ = v_isSharedCheck_4365_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4358_);
                        crate::leanh::lean_dec(v___x_4334_);
                        v___x_4360_ = crate::leanh::lean_box(0);
                        v_isShared_4361_ = v_isSharedCheck_4365_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4340_ = lean_st_ref_take(v_a_4323_);
                v_lemmas_4341_ = crate::leanh::lean_ctor_get(v___x_4340_, 0);
                v_bvExprCache_4342_ = crate::leanh::lean_ctor_get(v___x_4340_, 1);
                v_bvPredCache_4343_ = crate::leanh::lean_ctor_get(v___x_4340_, 2);
                v_bvLogicalCache_4344_ = crate::leanh::lean_ctor_get(v___x_4340_, 3);
                v_isSharedCheck_4356_ = (!crate::leanh::lean_is_exclusive(v___x_4340_)) as u8;
                if v_isSharedCheck_4356_ == 0 {
                    v___x_4346_ = v___x_4340_;
                    v_isShared_4347_ = v_isSharedCheck_4356_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_4344_);
                    crate::leanh::lean_inc(v_bvPredCache_4343_);
                    crate::leanh::lean_inc(v_bvExprCache_4342_);
                    crate::leanh::lean_inc(v_lemmas_4341_);
                    crate::leanh::lean_dec(v___x_4340_);
                    v___x_4346_ = crate::leanh::lean_box(0);
                    v_isShared_4347_ = v_isSharedCheck_4356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_4336_);
                v___x_4348_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4332_,
                    v___x_4333_,
                    v_bvPredCache_4343_,
                    v_e_4321_,
                    v_a_4336_,
                );
                if v_isShared_4347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4346_, 2, v___x_4348_);
                    v___x_4350_ = v___x_4346_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_lemmas_4341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_bvExprCache_4342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 2, v___x_4348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 3, v_bvLogicalCache_4344_);
                    v___x_4350_ = v_reuseFailAlloc_4355_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4351_ = lean_st_ref_set(v_a_4323_, v___x_4350_);
                if v_isShared_4339_ == 0 {
                    v___x_4353_ = v___x_4338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4336_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4353_;
            }
            5 => {
                if v_isShared_4361_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4360_, 0);
                    v___x_4363_ = v___x_4360_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_val_4358_);
                    v___x_4363_ = v_reuseFailAlloc_4364_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___boxed(
    mut v_e_4366_: *mut crate::leanh::LeanObject,
    mut v_f_4367_: *mut crate::leanh::LeanObject,
    mut v_a_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(
        v_e_4366_, v_f_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_,
    );
    crate::leanh::lean_dec(v_a_4373_);
    crate::leanh::lean_dec_ref(v_a_4372_);
    crate::leanh::lean_dec(v_a_4371_);
    crate::leanh::lean_dec_ref(v_a_4370_);
    crate::leanh::lean_dec(v_a_4369_);
    crate::leanh::lean_dec(v_a_4368_);
    return v_res_4375_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(
    mut v_e_4376_: *mut crate::leanh::LeanObject,
    mut v_f_4377_: *mut crate::leanh::LeanObject,
    mut v_a_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
    mut v_a_4380_: *mut crate::leanh::LeanObject,
    mut v_a_4381_: *mut crate::leanh::LeanObject,
    mut v_a_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4394_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_val_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4385_ = lean_st_ref_get(v_a_4378_);
                v_bvLogicalCache_4386_ = crate::leanh::lean_ctor_get(v___x_4385_, 3);
                crate::leanh::lean_inc_ref(v_bvLogicalCache_4386_);
                crate::leanh::lean_dec(v___x_4385_);
                v___x_4387_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0;
                v___x_4388_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1;
                crate::leanh::lean_inc_ref(v_e_4376_);
                v___x_4389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___x_4387_,
                    v___x_4388_,
                    v_bvLogicalCache_4386_,
                    v_e_4376_,
                );
                crate::leanh::lean_dec_ref(v_bvLogicalCache_4386_);
                if crate::leanh::lean_obj_tag(v___x_4389_) == 0 {
                    crate::leanh::lean_inc(v_a_4383_);
                    crate::leanh::lean_inc_ref(v_a_4382_);
                    crate::leanh::lean_inc(v_a_4381_);
                    crate::leanh::lean_inc_ref(v_a_4380_);
                    crate::leanh::lean_inc(v_a_4379_);
                    crate::leanh::lean_inc(v_a_4378_);
                    crate::leanh::lean_inc_ref(v_e_4376_);
                    v___x_4390_ = crate::leanh::lean_apply_8(
                        v_f_4377_,
                        v_e_4376_,
                        v_a_4378_,
                        v_a_4379_,
                        v_a_4380_,
                        v_a_4381_,
                        v_a_4382_,
                        v_a_4383_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4390_) == 0 {
                        v_a_4391_ = crate::leanh::lean_ctor_get(v___x_4390_, 0);
                        v_isSharedCheck_4412_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4390_)) as u8;
                        if v_isSharedCheck_4412_ == 0 {
                            v___x_4393_ = v___x_4390_;
                            v_isShared_4394_ = v_isSharedCheck_4412_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4391_);
                            crate::leanh::lean_dec(v___x_4390_);
                            v___x_4393_ = crate::leanh::lean_box(0);
                            v_isShared_4394_ = v_isSharedCheck_4412_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4376_);
                        return v___x_4390_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4377_);
                    crate::leanh::lean_dec_ref(v_e_4376_);
                    v_val_4413_ = crate::leanh::lean_ctor_get(v___x_4389_, 0);
                    v_isSharedCheck_4420_ = (!crate::leanh::lean_is_exclusive(v___x_4389_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4415_ = v___x_4389_;
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4413_);
                        crate::leanh::lean_dec(v___x_4389_);
                        v___x_4415_ = crate::leanh::lean_box(0);
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4395_ = lean_st_ref_take(v_a_4378_);
                v_lemmas_4396_ = crate::leanh::lean_ctor_get(v___x_4395_, 0);
                v_bvExprCache_4397_ = crate::leanh::lean_ctor_get(v___x_4395_, 1);
                v_bvPredCache_4398_ = crate::leanh::lean_ctor_get(v___x_4395_, 2);
                v_bvLogicalCache_4399_ = crate::leanh::lean_ctor_get(v___x_4395_, 3);
                v_isSharedCheck_4411_ = (!crate::leanh::lean_is_exclusive(v___x_4395_)) as u8;
                if v_isSharedCheck_4411_ == 0 {
                    v___x_4401_ = v___x_4395_;
                    v_isShared_4402_ = v_isSharedCheck_4411_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_4399_);
                    crate::leanh::lean_inc(v_bvPredCache_4398_);
                    crate::leanh::lean_inc(v_bvExprCache_4397_);
                    crate::leanh::lean_inc(v_lemmas_4396_);
                    crate::leanh::lean_dec(v___x_4395_);
                    v___x_4401_ = crate::leanh::lean_box(0);
                    v_isShared_4402_ = v_isSharedCheck_4411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_4391_);
                v___x_4403_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4387_,
                    v___x_4388_,
                    v_bvLogicalCache_4399_,
                    v_e_4376_,
                    v_a_4391_,
                );
                if v_isShared_4402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4401_, 3, v___x_4403_);
                    v___x_4405_ = v___x_4401_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4410_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_lemmas_4396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_bvExprCache_4397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 2, v_bvPredCache_4398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 3, v___x_4403_);
                    v___x_4405_ = v_reuseFailAlloc_4410_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4406_ = lean_st_ref_set(v_a_4378_, v___x_4405_);
                if v_isShared_4394_ == 0 {
                    v___x_4408_ = v___x_4393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4391_);
                    v___x_4408_ = v_reuseFailAlloc_4409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4408_;
            }
            5 => {
                if v_isShared_4416_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4415_, 0);
                    v___x_4418_ = v___x_4415_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_val_4413_);
                    v___x_4418_ = v_reuseFailAlloc_4419_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___boxed(
    mut v_e_4421_: *mut crate::leanh::LeanObject,
    mut v_f_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4430_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(
        v_e_4421_, v_f_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_,
    );
    crate::leanh::lean_dec(v_a_4428_);
    crate::leanh::lean_dec_ref(v_a_4427_);
    crate::leanh::lean_dec(v_a_4426_);
    crate::leanh::lean_dec_ref(v_a_4425_);
    crate::leanh::lean_dec(v_a_4424_);
    crate::leanh::lean_dec(v_a_4423_);
    return v_res_4430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp =
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp);
    l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp =
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp);
    l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred =
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred);
    l_Lean_Meta_Tactic_BVDecide_instToExprGate = _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprGate);
    l_Lean_Meta_Tactic_BVDecide_instToExprBVPred =
        _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
}
