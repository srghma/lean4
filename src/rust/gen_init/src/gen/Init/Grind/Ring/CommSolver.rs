// Lean compiler output
// Module: Init.Grind.Ring.CommSolver
// Imports: Init.Data.Ord.Basic Init.Grind.Ring.Field Init.Grind.Ordered.Ring Init.GrindInstances.Ring.Int Init.Data.Ord.Basic Init.LawfulBEqTactics Init.Classical Init.Data.Bool Init.Data.Int.DivMod.Lemmas Init.Data.RArray Init.Ext Init.Data.Hashable Init.Data.Int.LemmasAux Init.Data.Nat.Linear Init.Grind.Ordered.Order Init.Omega Init.WFTactics Init.Data.Int.Repr
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, l_Int_decidableDvd,
    runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Int::Repr::{
    initialize_Init_Data_Int_Repr, l_Int_repr, runtime_initialize_Init_Data_Int_Repr,
};
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, l_instDecidableEqOrdering,
    runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, l_Lean_RArray_getImpl___redArg,
    runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Grind::Ordered::Order::{
    initialize_Init_Grind_Ordered_Order, runtime_initialize_Init_Grind_Ordered_Order,
};
use crate::r#gen::Init::Grind::Ordered::Ring::{
    initialize_Init_Grind_Ordered_Ring, runtime_initialize_Init_Grind_Ordered_Ring,
};
use crate::r#gen::Init::Grind::Ring::Basic::l_Lean_Grind_Ring_toIntModule___redArg;
use crate::r#gen::Init::Grind::Ring::Field::{
    initialize_Init_Grind_Ring_Field, runtime_initialize_Init_Grind_Ring_Field,
};
use crate::r#gen::Init::GrindInstances::Ring::Int::{
    initialize_Init_GrindInstances_Ring_Int, runtime_initialize_Init_GrindInstances_Ring_Int,
};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_abs,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash,
};
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedExpr_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedExpr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instBEqExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instHashableExpr___closed__0_value:
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
    m_fun: l_Lean_Grind_CommRing_instHashableExpr_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instHashableExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashableExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 110, 117, 109, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 110, 97, 116, 67, 97, 115, 116, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 105, 110, 116, 67, 97, 115, 116, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__13_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__16_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__19_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 115, 117, 98, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__22_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 109, 117, 108, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__25_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        69, 120, 112, 114, 46, 112, 111, 119, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__28_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_CommRing_instReprExpr_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instReprExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instBEqPower___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_CommRing_instBEqPower_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instBEqPower___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqPower: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value:
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
        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value:
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
        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9_value:
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
        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [107, 0],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11_value:
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
        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15_value:
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
        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16_value:
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
        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_CommRing_instReprPower_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instReprPower___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprPower: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instInhabitedPower_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instInhabitedPower: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instHashablePower___closed__0_value:
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
    m_fun: l_Lean_Grind_CommRing_instHashablePower_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instHashablePower___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashablePower: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instBEqMon___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqMon_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqMon___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqMon___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqMon: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqMon___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        77, 111, 110, 46, 117, 110, 105, 116, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        77, 111, 110, 46, 109, 117, 108, 116, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__4_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instReprMon_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instReprMon___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprMon: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instInhabitedMon_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedMon: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instHashableMon___closed__0_value:
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
    m_fun: l_Lean_Grind_CommRing_instHashableMon_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instHashableMon___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableMon___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashableMon: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableMon___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_hugeFuel: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instBEqPoly___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqPoly_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqPoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqPoly: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        80, 111, 108, 121, 46, 110, 117, 109, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46,
        80, 111, 108, 121, 46, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_CommRing_instReprPoly_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instReprPoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprPoly: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedPoly_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedPoly: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instHashablePoly___closed__0_value:
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
    m_fun: l_Lean_Grind_CommRing_instHashablePoly_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_CommRing_instHashablePoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashablePoly: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_Poly_pow___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Poly_pow___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Expr_toPoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorIdx(
    mut v_x_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3770_) {
        0 => {
            let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3771_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3771_;
        }
        1 => {
            let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3772_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3772_;
        }
        2 => {
            let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3773_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3773_;
        }
        3 => {
            let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3774_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3774_;
        }
        4 => {
            let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3775_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3775_;
        }
        5 => {
            let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3776_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_3776_;
        }
        6 => {
            let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3777_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_3777_;
        }
        7 => {
            let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3778_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_3778_;
        }
        _ => {
            let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3779_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_3779_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorIdx___boxed(
    mut v_x_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Lean_Grind_CommRing_Expr_ctorIdx(v_x_3780_);
    crate::leanh::lean_dec_ref(v_x_3780_);
    return v_res_3781_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorElim___redArg(
    mut v_t_3782_: *mut crate::leanh::LeanObject,
    mut v_k_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_3782_) {
        4 => {
            let mut v_a_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3784_ = crate::leanh::lean_ctor_get(v_t_3782_, 0);
            crate::leanh::lean_inc_ref(v_a_3784_);
            crate::leanh::lean_dec_ref_known(v_t_3782_, 1);
            v___x_3785_ = crate::leanh::lean_apply_1(v_k_3783_, v_a_3784_);
            return v___x_3785_;
        }
        5 => {
            let mut v_a_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3786_ = crate::leanh::lean_ctor_get(v_t_3782_, 0);
            crate::leanh::lean_inc_ref(v_a_3786_);
            v_b_3787_ = crate::leanh::lean_ctor_get(v_t_3782_, 1);
            crate::leanh::lean_inc_ref(v_b_3787_);
            crate::leanh::lean_dec_ref_known(v_t_3782_, 2);
            v___x_3788_ = crate::leanh::lean_apply_2(v_k_3783_, v_a_3786_, v_b_3787_);
            return v___x_3788_;
        }
        6 => {
            let mut v_a_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3789_ = crate::leanh::lean_ctor_get(v_t_3782_, 0);
            crate::leanh::lean_inc_ref(v_a_3789_);
            v_b_3790_ = crate::leanh::lean_ctor_get(v_t_3782_, 1);
            crate::leanh::lean_inc_ref(v_b_3790_);
            crate::leanh::lean_dec_ref_known(v_t_3782_, 2);
            v___x_3791_ = crate::leanh::lean_apply_2(v_k_3783_, v_a_3789_, v_b_3790_);
            return v___x_3791_;
        }
        7 => {
            let mut v_a_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3792_ = crate::leanh::lean_ctor_get(v_t_3782_, 0);
            crate::leanh::lean_inc_ref(v_a_3792_);
            v_b_3793_ = crate::leanh::lean_ctor_get(v_t_3782_, 1);
            crate::leanh::lean_inc_ref(v_b_3793_);
            crate::leanh::lean_dec_ref_known(v_t_3782_, 2);
            v___x_3794_ = crate::leanh::lean_apply_2(v_k_3783_, v_a_3792_, v_b_3793_);
            return v___x_3794_;
        }
        8 => {
            let mut v_a_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3795_ = crate::leanh::lean_ctor_get(v_t_3782_, 0);
            crate::leanh::lean_inc_ref(v_a_3795_);
            v_k_3796_ = crate::leanh::lean_ctor_get(v_t_3782_, 1);
            crate::leanh::lean_inc(v_k_3796_);
            crate::leanh::lean_dec_ref_known(v_t_3782_, 2);
            v___x_3797_ = crate::leanh::lean_apply_2(v_k_3783_, v_a_3795_, v_k_3796_);
            return v___x_3797_;
        }
        _ => {
            let mut v_k_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_3798_ = crate::leanh::lean_ctor_get(v_t_3782_, 0);
            crate::leanh::lean_inc(v_k_3798_);
            crate::leanh::lean_dec_ref(v_t_3782_);
            v___x_3799_ = crate::leanh::lean_apply_1(v_k_3783_, v_k_3798_);
            return v___x_3799_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorElim(
    mut v_motive_3800_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3801_: *mut crate::leanh::LeanObject,
    mut v_t_3802_: *mut crate::leanh::LeanObject,
    mut v_h_3803_: *mut crate::leanh::LeanObject,
    mut v_k_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3805_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3802_, v_k_3804_);
    return v___x_3805_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorElim___boxed(
    mut v_motive_3806_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3807_: *mut crate::leanh::LeanObject,
    mut v_t_3808_: *mut crate::leanh::LeanObject,
    mut v_h_3809_: *mut crate::leanh::LeanObject,
    mut v_k_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3811_ = l_Lean_Grind_CommRing_Expr_ctorElim(
        v_motive_3806_,
        v_ctorIdx_3807_,
        v_t_3808_,
        v_h_3809_,
        v_k_3810_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3807_);
    return v_res_3811_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_num_elim___redArg(
    mut v_t_3812_: *mut crate::leanh::LeanObject,
    mut v_num_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3812_, v_num_3813_);
    return v___x_3814_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_num_elim(
    mut v_motive_3815_: *mut crate::leanh::LeanObject,
    mut v_t_3816_: *mut crate::leanh::LeanObject,
    mut v_h_3817_: *mut crate::leanh::LeanObject,
    mut v_num_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3819_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3816_, v_num_3818_);
    return v___x_3819_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(
    mut v_t_3820_: *mut crate::leanh::LeanObject,
    mut v_natCast_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3822_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3820_, v_natCast_3821_);
    return v___x_3822_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_natCast_elim(
    mut v_motive_3823_: *mut crate::leanh::LeanObject,
    mut v_t_3824_: *mut crate::leanh::LeanObject,
    mut v_h_3825_: *mut crate::leanh::LeanObject,
    mut v_natCast_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3824_, v_natCast_3826_);
    return v___x_3827_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(
    mut v_t_3828_: *mut crate::leanh::LeanObject,
    mut v_intCast_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3828_, v_intCast_3829_);
    return v___x_3830_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_intCast_elim(
    mut v_motive_3831_: *mut crate::leanh::LeanObject,
    mut v_t_3832_: *mut crate::leanh::LeanObject,
    mut v_h_3833_: *mut crate::leanh::LeanObject,
    mut v_intCast_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3835_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3832_, v_intCast_3834_);
    return v___x_3835_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_var_elim___redArg(
    mut v_t_3836_: *mut crate::leanh::LeanObject,
    mut v_var_3837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3838_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3836_, v_var_3837_);
    return v___x_3838_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_var_elim(
    mut v_motive_3839_: *mut crate::leanh::LeanObject,
    mut v_t_3840_: *mut crate::leanh::LeanObject,
    mut v_h_3841_: *mut crate::leanh::LeanObject,
    mut v_var_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3840_, v_var_3842_);
    return v___x_3843_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_neg_elim___redArg(
    mut v_t_3844_: *mut crate::leanh::LeanObject,
    mut v_neg_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3844_, v_neg_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_neg_elim(
    mut v_motive_3847_: *mut crate::leanh::LeanObject,
    mut v_t_3848_: *mut crate::leanh::LeanObject,
    mut v_h_3849_: *mut crate::leanh::LeanObject,
    mut v_neg_3850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3848_, v_neg_3850_);
    return v___x_3851_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_add_elim___redArg(
    mut v_t_3852_: *mut crate::leanh::LeanObject,
    mut v_add_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3852_, v_add_3853_);
    return v___x_3854_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_add_elim(
    mut v_motive_3855_: *mut crate::leanh::LeanObject,
    mut v_t_3856_: *mut crate::leanh::LeanObject,
    mut v_h_3857_: *mut crate::leanh::LeanObject,
    mut v_add_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3856_, v_add_3858_);
    return v___x_3859_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_sub_elim___redArg(
    mut v_t_3860_: *mut crate::leanh::LeanObject,
    mut v_sub_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3862_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3860_, v_sub_3861_);
    return v___x_3862_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_sub_elim(
    mut v_motive_3863_: *mut crate::leanh::LeanObject,
    mut v_t_3864_: *mut crate::leanh::LeanObject,
    mut v_h_3865_: *mut crate::leanh::LeanObject,
    mut v_sub_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3864_, v_sub_3866_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_mul_elim___redArg(
    mut v_t_3868_: *mut crate::leanh::LeanObject,
    mut v_mul_3869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3868_, v_mul_3869_);
    return v___x_3870_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_mul_elim(
    mut v_motive_3871_: *mut crate::leanh::LeanObject,
    mut v_t_3872_: *mut crate::leanh::LeanObject,
    mut v_h_3873_: *mut crate::leanh::LeanObject,
    mut v_mul_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3872_, v_mul_3874_);
    return v___x_3875_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_pow_elim___redArg(
    mut v_t_3876_: *mut crate::leanh::LeanObject,
    mut v_pow_3877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3876_, v_pow_3877_);
    return v___x_3878_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_pow_elim(
    mut v_motive_3879_: *mut crate::leanh::LeanObject,
    mut v_t_3880_: *mut crate::leanh::LeanObject,
    mut v_h_3881_: *mut crate::leanh::LeanObject,
    mut v_pow_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3883_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3880_, v_pow_3882_);
    return v___x_3883_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3885_ = lean_nat_to_int(v___x_3884_);
    return v___x_3885_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_3887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3887_, 0, v___x_3886_);
    return v___x_3887_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3888_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1,
    );
    return v___x_3888_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr() -> *mut crate::leanh::LeanObject {
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3889_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
    return v___x_3889_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqExpr_beq(
    mut v_x_3890_: *mut crate::leanh::LeanObject,
    mut v_x_3891_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: u8 = 0;
    let mut v_k_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: u8 = 0;
    let mut v_k_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: u8 = 0;
    let mut v_k_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: u8 = 0;
    let mut v_i_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: u8 = 0;
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: u8 = 0;
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: u8 = 0;
    let mut v_a_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v_a_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v_a_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3890_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 0 {
                        v_k_3899_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_k_3900_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v___x_3901_ = lean_int_dec_eq(v_k_3899_, v_k_3900_);
                        return v___x_3901_;
                    } else {
                        v___x_3902_ = 0;
                        return v___x_3902_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 1 {
                        v_k_3903_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_k_3904_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v___x_3905_ = lean_nat_dec_eq(v_k_3903_, v_k_3904_);
                        return v___x_3905_;
                    } else {
                        v___x_3906_ = 0;
                        return v___x_3906_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 2 {
                        v_k_3907_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_k_3908_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v___x_3909_ = lean_int_dec_eq(v_k_3907_, v_k_3908_);
                        return v___x_3909_;
                    } else {
                        v___x_3910_ = 0;
                        return v___x_3910_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 3 {
                        v_i_3911_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_i_3912_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v___x_3913_ = lean_nat_dec_eq(v_i_3911_, v_i_3912_);
                        return v___x_3913_;
                    } else {
                        v___x_3914_ = 0;
                        return v___x_3914_;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 4 {
                        v_a_3915_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_a_3916_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v_x_3890_ = v_a_3915_;
                        v_x_3891_ = v_a_3916_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3918_ = 0;
                        return v___x_3918_;
                    }
                }
                5 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 5 {
                        v_a_3919_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_b_3920_ = crate::leanh::lean_ctor_get(v_x_3890_, 1);
                        v_a_3921_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v_b_3922_ = crate::leanh::lean_ctor_get(v_x_3891_, 1);
                        v_a_3893_ = v_a_3919_;
                        v_a_3894_ = v_b_3920_;
                        v_b_3895_ = v_a_3921_;
                        v_b_3896_ = v_b_3922_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3923_ = 0;
                        return v___x_3923_;
                    }
                }
                6 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 6 {
                        v_a_3924_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_b_3925_ = crate::leanh::lean_ctor_get(v_x_3890_, 1);
                        v_a_3926_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v_b_3927_ = crate::leanh::lean_ctor_get(v_x_3891_, 1);
                        v_a_3893_ = v_a_3924_;
                        v_a_3894_ = v_b_3925_;
                        v_b_3895_ = v_a_3926_;
                        v_b_3896_ = v_b_3927_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3928_ = 0;
                        return v___x_3928_;
                    }
                }
                7 => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 7 {
                        v_a_3929_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_b_3930_ = crate::leanh::lean_ctor_get(v_x_3890_, 1);
                        v_a_3931_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v_b_3932_ = crate::leanh::lean_ctor_get(v_x_3891_, 1);
                        v_a_3893_ = v_a_3929_;
                        v_a_3894_ = v_b_3930_;
                        v_b_3895_ = v_a_3931_;
                        v_b_3896_ = v_b_3932_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3933_ = 0;
                        return v___x_3933_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_3891_) == 8 {
                        v_a_3934_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                        v_k_3935_ = crate::leanh::lean_ctor_get(v_x_3890_, 1);
                        v_a_3936_ = crate::leanh::lean_ctor_get(v_x_3891_, 0);
                        v_k_3937_ = crate::leanh::lean_ctor_get(v_x_3891_, 1);
                        v___x_3938_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_a_3934_, v_a_3936_);
                        if v___x_3938_ == 0 {
                            return v___x_3938_;
                        } else {
                            v___x_3939_ = lean_nat_dec_eq(v_k_3935_, v_k_3937_);
                            return v___x_3939_;
                        }
                    } else {
                        v___x_3940_ = 0;
                        return v___x_3940_;
                    }
                }
            },
            1 => {
                v___x_3897_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_a_3893_, v_b_3895_);
                if v___x_3897_ == 0 {
                    return v___x_3897_;
                } else {
                    v_x_3890_ = v_a_3894_;
                    v_x_3891_ = v_b_3896_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(
    mut v_x_3941_: *mut crate::leanh::LeanObject,
    mut v_x_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3943_: u8 = 0;
    let mut v_r_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_x_3941_, v_x_3942_);
    crate::leanh::lean_dec_ref(v_x_3942_);
    crate::leanh::lean_dec_ref(v_x_3941_);
    v_r_3944_ = crate::leanh::lean_box((v_res_3943_) as usize);
    return v_r_3944_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableExpr_hash(
    mut v_x_3947_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_3947_) {
        0 => {
            let mut v_k_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3949_: u64 = 0;
            let mut v_intZero_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isNeg_3951_: u8 = 0;
            v_k_3948_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v___x_3949_ = 0u64;
            v_intZero_3950_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                ),
                _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
            );
            v_isNeg_3951_ = lean_int_dec_lt(v_k_3948_, v_intZero_3950_);
            if v_isNeg_3951_ == 0 {
                let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3955_: u64 = 0;
                let mut v___x_3956_: u64 = 0;
                v_a_3952_ = lean_nat_abs(v_k_3948_);
                v___x_3953_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3954_ = lean_nat_mul(v___x_3953_, v_a_3952_);
                crate::leanh::lean_dec(v_a_3952_);
                v___x_3955_ = lean_uint64_of_nat(v___x_3954_);
                crate::leanh::lean_dec(v___x_3954_);
                v___x_3956_ = lean_uint64_mix_hash(v___x_3949_, v___x_3955_);
                return v___x_3956_;
            } else {
                let mut v_abs_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3963_: u64 = 0;
                let mut v___x_3964_: u64 = 0;
                v_abs_3957_ = lean_nat_abs(v_k_3948_);
                v_one_3958_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_3959_ = lean_nat_sub(v_abs_3957_, v_one_3958_);
                crate::leanh::lean_dec(v_abs_3957_);
                v___x_3960_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3961_ = lean_nat_mul(v___x_3960_, v_a_3959_);
                crate::leanh::lean_dec(v_a_3959_);
                v___x_3962_ = lean_nat_add(v___x_3961_, v_one_3958_);
                crate::leanh::lean_dec(v___x_3961_);
                v___x_3963_ = lean_uint64_of_nat(v___x_3962_);
                crate::leanh::lean_dec(v___x_3962_);
                v___x_3964_ = lean_uint64_mix_hash(v___x_3949_, v___x_3963_);
                return v___x_3964_;
            }
        }
        1 => {
            let mut v_k_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3966_: u64 = 0;
            let mut v___x_3967_: u64 = 0;
            let mut v___x_3968_: u64 = 0;
            v_k_3965_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v___x_3966_ = 1u64;
            v___x_3967_ = lean_uint64_of_nat(v_k_3965_);
            v___x_3968_ = lean_uint64_mix_hash(v___x_3966_, v___x_3967_);
            return v___x_3968_;
        }
        2 => {
            let mut v_k_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3970_: u64 = 0;
            let mut v_intZero_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isNeg_3972_: u8 = 0;
            v_k_3969_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v___x_3970_ = 2u64;
            v_intZero_3971_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                ),
                _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
            );
            v_isNeg_3972_ = lean_int_dec_lt(v_k_3969_, v_intZero_3971_);
            if v_isNeg_3972_ == 0 {
                let mut v_a_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3976_: u64 = 0;
                let mut v___x_3977_: u64 = 0;
                v_a_3973_ = lean_nat_abs(v_k_3969_);
                v___x_3974_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3975_ = lean_nat_mul(v___x_3974_, v_a_3973_);
                crate::leanh::lean_dec(v_a_3973_);
                v___x_3976_ = lean_uint64_of_nat(v___x_3975_);
                crate::leanh::lean_dec(v___x_3975_);
                v___x_3977_ = lean_uint64_mix_hash(v___x_3970_, v___x_3976_);
                return v___x_3977_;
            } else {
                let mut v_abs_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3984_: u64 = 0;
                let mut v___x_3985_: u64 = 0;
                v_abs_3978_ = lean_nat_abs(v_k_3969_);
                v_one_3979_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_3980_ = lean_nat_sub(v_abs_3978_, v_one_3979_);
                crate::leanh::lean_dec(v_abs_3978_);
                v___x_3981_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3982_ = lean_nat_mul(v___x_3981_, v_a_3980_);
                crate::leanh::lean_dec(v_a_3980_);
                v___x_3983_ = lean_nat_add(v___x_3982_, v_one_3979_);
                crate::leanh::lean_dec(v___x_3982_);
                v___x_3984_ = lean_uint64_of_nat(v___x_3983_);
                crate::leanh::lean_dec(v___x_3983_);
                v___x_3985_ = lean_uint64_mix_hash(v___x_3970_, v___x_3984_);
                return v___x_3985_;
            }
        }
        3 => {
            let mut v_i_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3987_: u64 = 0;
            let mut v___x_3988_: u64 = 0;
            let mut v___x_3989_: u64 = 0;
            v_i_3986_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v___x_3987_ = 3u64;
            v___x_3988_ = lean_uint64_of_nat(v_i_3986_);
            v___x_3989_ = lean_uint64_mix_hash(v___x_3987_, v___x_3988_);
            return v___x_3989_;
        }
        4 => {
            let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3991_: u64 = 0;
            let mut v___x_3992_: u64 = 0;
            let mut v___x_3993_: u64 = 0;
            v_a_3990_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v___x_3991_ = 4u64;
            v___x_3992_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_3990_);
            v___x_3993_ = lean_uint64_mix_hash(v___x_3991_, v___x_3992_);
            return v___x_3993_;
        }
        5 => {
            let mut v_a_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3996_: u64 = 0;
            let mut v___x_3997_: u64 = 0;
            let mut v___x_3998_: u64 = 0;
            let mut v___x_3999_: u64 = 0;
            let mut v___x_4000_: u64 = 0;
            v_a_3994_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v_b_3995_ = crate::leanh::lean_ctor_get(v_x_3947_, 1);
            v___x_3996_ = 5u64;
            v___x_3997_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_3994_);
            v___x_3998_ = lean_uint64_mix_hash(v___x_3996_, v___x_3997_);
            v___x_3999_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_3995_);
            v___x_4000_ = lean_uint64_mix_hash(v___x_3998_, v___x_3999_);
            return v___x_4000_;
        }
        6 => {
            let mut v_a_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4003_: u64 = 0;
            let mut v___x_4004_: u64 = 0;
            let mut v___x_4005_: u64 = 0;
            let mut v___x_4006_: u64 = 0;
            let mut v___x_4007_: u64 = 0;
            v_a_4001_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v_b_4002_ = crate::leanh::lean_ctor_get(v_x_3947_, 1);
            v___x_4003_ = 6u64;
            v___x_4004_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_4001_);
            v___x_4005_ = lean_uint64_mix_hash(v___x_4003_, v___x_4004_);
            v___x_4006_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_4002_);
            v___x_4007_ = lean_uint64_mix_hash(v___x_4005_, v___x_4006_);
            return v___x_4007_;
        }
        7 => {
            let mut v_a_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4010_: u64 = 0;
            let mut v___x_4011_: u64 = 0;
            let mut v___x_4012_: u64 = 0;
            let mut v___x_4013_: u64 = 0;
            let mut v___x_4014_: u64 = 0;
            v_a_4008_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v_b_4009_ = crate::leanh::lean_ctor_get(v_x_3947_, 1);
            v___x_4010_ = 7u64;
            v___x_4011_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_4008_);
            v___x_4012_ = lean_uint64_mix_hash(v___x_4010_, v___x_4011_);
            v___x_4013_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_4009_);
            v___x_4014_ = lean_uint64_mix_hash(v___x_4012_, v___x_4013_);
            return v___x_4014_;
        }
        _ => {
            let mut v_a_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4017_: u64 = 0;
            let mut v___x_4018_: u64 = 0;
            let mut v___x_4019_: u64 = 0;
            let mut v___x_4020_: u64 = 0;
            let mut v___x_4021_: u64 = 0;
            v_a_4015_ = crate::leanh::lean_ctor_get(v_x_3947_, 0);
            v_k_4016_ = crate::leanh::lean_ctor_get(v_x_3947_, 1);
            v___x_4017_ = 8u64;
            v___x_4018_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_4015_);
            v___x_4019_ = lean_uint64_mix_hash(v___x_4017_, v___x_4018_);
            v___x_4020_ = lean_uint64_of_nat(v_k_4016_);
            v___x_4021_ = lean_uint64_mix_hash(v___x_4019_, v___x_4020_);
            return v___x_4021_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(
    mut v_x_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4023_: u64 = 0;
    let mut v_r_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_x_4022_);
    crate::leanh::lean_dec_ref(v_x_4022_);
    v_r_4024_ = crate::leanh::lean_box_uint64(v_res_4023_);
    return v_r_4024_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4034_ = lean_nat_to_int(v___x_4033_);
    return v___x_4034_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4036_ = lean_nat_to_int(v___x_4035_);
    return v___x_4036_;
}
pub unsafe fn l_Lean_Grind_CommRing_instReprExpr_repr(
    mut v_x_4085_: *mut crate::leanh::LeanObject,
    mut v_prec_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___y_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_k_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___y_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v_k_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___y_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut v_i_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___y_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_a_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_a_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v_a_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: u8 = 0;
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4085_) {
                0 => {
                    v_k_4105_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4128_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4107_ = v_x_4085_;
                        v_isShared_4108_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4105_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4107_ = crate::leanh::lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_k_4129_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4149_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4149_ == 0 {
                        v___x_4131_ = v_x_4085_;
                        v_isShared_4132_ = v_isSharedCheck_4149_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4129_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4131_ = crate::leanh::lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4149_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_k_4150_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4173_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4173_ == 0 {
                        v___x_4152_ = v_x_4085_;
                        v_isShared_4153_ = v_isSharedCheck_4173_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4150_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4152_ = crate::leanh::lean_box(0);
                        v_isShared_4153_ = v_isSharedCheck_4173_;
                        state = 10;
                        continue;
                    }
                }
                3 => {
                    v_i_4174_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4194_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4194_ == 0 {
                        v___x_4176_ = v_x_4085_;
                        v_isShared_4177_ = v_isSharedCheck_4194_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_4174_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4176_ = crate::leanh::lean_box(0);
                        v_isShared_4177_ = v_isSharedCheck_4194_;
                        state = 14;
                        continue;
                    }
                }
                4 => {
                    v_a_4195_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    crate::leanh::lean_inc_ref(v_a_4195_);
                    crate::leanh::lean_dec_ref_known(v_x_4085_, 1);
                    v___x_4196_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4206_ = lean_nat_dec_le(v___x_4196_, v_prec_4086_);
                    if v___x_4206_ == 0 {
                        v___x_4207_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                        );
                        v___y_4198_ = v___x_4207_;
                        state = 17;
                        continue;
                    } else {
                        v___x_4208_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                            ),
                            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                        );
                        v___y_4198_ = v___x_4208_;
                        state = 17;
                        continue;
                    }
                }
                5 => {
                    v_a_4209_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_b_4210_ = crate::leanh::lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4233_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4212_ = v_x_4085_;
                        v_isShared_4213_ = v_isSharedCheck_4233_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_4210_);
                        crate::leanh::lean_inc(v_a_4209_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4212_ = crate::leanh::lean_box(0);
                        v_isShared_4213_ = v_isSharedCheck_4233_;
                        state = 18;
                        continue;
                    }
                }
                6 => {
                    v_a_4234_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_b_4235_ = crate::leanh::lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4258_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4258_ == 0 {
                        v___x_4237_ = v_x_4085_;
                        v_isShared_4238_ = v_isSharedCheck_4258_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_4235_);
                        crate::leanh::lean_inc(v_a_4234_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4237_ = crate::leanh::lean_box(0);
                        v_isShared_4238_ = v_isSharedCheck_4258_;
                        state = 21;
                        continue;
                    }
                }
                7 => {
                    v_a_4259_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_b_4260_ = crate::leanh::lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4283_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4283_ == 0 {
                        v___x_4262_ = v_x_4085_;
                        v_isShared_4263_ = v_isSharedCheck_4283_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_4260_);
                        crate::leanh::lean_inc(v_a_4259_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4262_ = crate::leanh::lean_box(0);
                        v_isShared_4263_ = v_isSharedCheck_4283_;
                        state = 24;
                        continue;
                    }
                }
                _ => {
                    v_a_4284_ = crate::leanh::lean_ctor_get(v_x_4085_, 0);
                    v_k_4285_ = crate::leanh::lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4309_ = (!crate::leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4287_ = v_x_4085_;
                        v_isShared_4288_ = v_isSharedCheck_4309_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4285_);
                        crate::leanh::lean_inc(v_a_4284_);
                        crate::leanh::lean_dec(v_x_4085_);
                        v___x_4287_ = crate::leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4309_;
                        state = 27;
                        continue;
                    }
                }
            },
            1 => {
                crate::leanh::lean_inc(v___y_4089_);
                v___x_4091_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4091_, 0, v___y_4089_);
                crate::leanh::lean_ctor_set(v___x_4091_, 1, v___y_4090_);
                crate::leanh::lean_inc(v___y_4088_);
                v___x_4092_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4092_, 0, v___y_4088_);
                crate::leanh::lean_ctor_set(v___x_4092_, 1, v___x_4091_);
                v___x_4093_ = 0;
                v___x_4094_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4094_, 0, v___x_4092_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4094_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4093_,
                );
                v___x_4095_ = l_Repr_addAppParen(v___x_4094_, v_prec_4086_);
                return v___x_4095_;
            }
            2 => {
                crate::leanh::lean_inc(v___y_4098_);
                v___x_4100_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4100_, 0, v___y_4098_);
                crate::leanh::lean_ctor_set(v___x_4100_, 1, v___y_4099_);
                crate::leanh::lean_inc(v___y_4097_);
                v___x_4101_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4101_, 0, v___y_4097_);
                crate::leanh::lean_ctor_set(v___x_4101_, 1, v___x_4100_);
                v___x_4102_ = 0;
                v___x_4103_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4103_, 0, v___x_4101_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4103_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4102_,
                );
                v___x_4104_ = l_Repr_addAppParen(v___x_4103_, v_prec_4086_);
                return v___x_4104_;
            }
            3 => {
                v___x_4124_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4125_ = lean_nat_dec_le(v___x_4124_, v_prec_4086_);
                if v___x_4125_ == 0 {
                    v___x_4126_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4110_ = v___x_4126_;
                    state = 4;
                    continue;
                } else {
                    v___x_4127_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4110_ = v___x_4127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4111_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__2;
                v___x_4112_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_4113_ = lean_int_dec_lt(v_k_4105_, v___x_4112_);
                if v___x_4113_ == 0 {
                    v___x_4114_ = l_Int_repr(v_k_4105_);
                    crate::leanh::lean_dec(v_k_4105_);
                    if v_isShared_4108_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4107_, 3);
                        crate::leanh::lean_ctor_set(v___x_4107_, 0, v___x_4114_);
                        v___x_4116_ = v___x_4107_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4117_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
                        v___x_4116_ = v_reuseFailAlloc_4117_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_4118_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4119_ = l_Int_repr(v_k_4105_);
                    crate::leanh::lean_dec(v_k_4105_);
                    if v_isShared_4108_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4107_, 3);
                        crate::leanh::lean_ctor_set(v___x_4107_, 0, v___x_4119_);
                        v___x_4121_ = v___x_4107_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4123_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4119_);
                        v___x_4121_ = v_reuseFailAlloc_4123_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4097_ = v___y_4110_;
                v___y_4098_ = v___x_4111_;
                v___y_4099_ = v___x_4116_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4122_ = l_Repr_addAppParen(v___x_4121_, v___x_4118_);
                v___y_4097_ = v___y_4110_;
                v___y_4098_ = v___x_4111_;
                v___y_4099_ = v___x_4122_;
                state = 2;
                continue;
            }
            7 => {
                v___x_4145_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4146_ = lean_nat_dec_le(v___x_4145_, v_prec_4086_);
                if v___x_4146_ == 0 {
                    v___x_4147_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4134_ = v___x_4147_;
                    state = 8;
                    continue;
                } else {
                    v___x_4148_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4134_ = v___x_4148_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4135_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__7;
                v___x_4136_ = l_Nat_reprFast(v_k_4129_);
                if v_isShared_4132_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4131_, 3);
                    crate::leanh::lean_ctor_set(v___x_4131_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4131_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4144_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4144_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4139_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4139_, 0, v___x_4135_);
                crate::leanh::lean_ctor_set(v___x_4139_, 1, v___x_4138_);
                crate::leanh::lean_inc(v___y_4134_);
                v___x_4140_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4140_, 0, v___y_4134_);
                crate::leanh::lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = 0;
                v___x_4142_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4142_, 0, v___x_4140_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4141_,
                );
                v___x_4143_ = l_Repr_addAppParen(v___x_4142_, v_prec_4086_);
                return v___x_4143_;
            }
            10 => {
                v___x_4169_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4170_ = lean_nat_dec_le(v___x_4169_, v_prec_4086_);
                if v___x_4170_ == 0 {
                    v___x_4171_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4155_ = v___x_4171_;
                    state = 11;
                    continue;
                } else {
                    v___x_4172_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4155_ = v___x_4172_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4156_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__10;
                v___x_4157_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_4158_ = lean_int_dec_lt(v_k_4150_, v___x_4157_);
                if v___x_4158_ == 0 {
                    v___x_4159_ = l_Int_repr(v_k_4150_);
                    crate::leanh::lean_dec(v_k_4150_);
                    if v_isShared_4153_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4152_, 3);
                        crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4159_);
                        v___x_4161_ = v___x_4152_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4162_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
                        v___x_4161_ = v_reuseFailAlloc_4162_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_4163_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4164_ = l_Int_repr(v_k_4150_);
                    crate::leanh::lean_dec(v_k_4150_);
                    if v_isShared_4153_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4152_, 3);
                        crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4164_);
                        v___x_4166_ = v___x_4152_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4168_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
                        v___x_4166_ = v_reuseFailAlloc_4168_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v___y_4088_ = v___y_4155_;
                v___y_4089_ = v___x_4156_;
                v___y_4090_ = v___x_4161_;
                state = 1;
                continue;
            }
            13 => {
                v___x_4167_ = l_Repr_addAppParen(v___x_4166_, v___x_4163_);
                v___y_4088_ = v___y_4155_;
                v___y_4089_ = v___x_4156_;
                v___y_4090_ = v___x_4167_;
                state = 1;
                continue;
            }
            14 => {
                v___x_4190_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4191_ = lean_nat_dec_le(v___x_4190_, v_prec_4086_);
                if v___x_4191_ == 0 {
                    v___x_4192_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4179_ = v___x_4192_;
                    state = 15;
                    continue;
                } else {
                    v___x_4193_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4179_ = v___x_4193_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4180_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__13;
                v___x_4181_ = l_Nat_reprFast(v_i_4174_);
                if v_isShared_4177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4176_, 0, v___x_4181_);
                    v___x_4183_ = v___x_4176_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4181_);
                    v___x_4183_ = v_reuseFailAlloc_4189_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4184_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4184_, 0, v___x_4180_);
                crate::leanh::lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                crate::leanh::lean_inc(v___y_4179_);
                v___x_4185_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4185_, 0, v___y_4179_);
                crate::leanh::lean_ctor_set(v___x_4185_, 1, v___x_4184_);
                v___x_4186_ = 0;
                v___x_4187_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4187_, 0, v___x_4185_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4187_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4186_,
                );
                v___x_4188_ = l_Repr_addAppParen(v___x_4187_, v_prec_4086_);
                return v___x_4188_;
            }
            17 => {
                v___x_4199_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__16;
                v___x_4200_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4195_, v___x_4196_);
                v___x_4201_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4201_, 0, v___x_4199_);
                crate::leanh::lean_ctor_set(v___x_4201_, 1, v___x_4200_);
                crate::leanh::lean_inc(v___y_4198_);
                v___x_4202_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4202_, 0, v___y_4198_);
                crate::leanh::lean_ctor_set(v___x_4202_, 1, v___x_4201_);
                v___x_4203_ = 0;
                v___x_4204_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4202_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4204_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4203_,
                );
                v___x_4205_ = l_Repr_addAppParen(v___x_4204_, v_prec_4086_);
                return v___x_4205_;
            }
            18 => {
                v___x_4214_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4230_ = lean_nat_dec_le(v___x_4214_, v_prec_4086_);
                if v___x_4230_ == 0 {
                    v___x_4231_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4216_ = v___x_4231_;
                    state = 19;
                    continue;
                } else {
                    v___x_4232_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4216_ = v___x_4232_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_4217_ = crate::leanh::lean_box(1);
                v___x_4218_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__19;
                v___x_4219_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4209_, v___x_4214_);
                if v_isShared_4213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4212_, 1, v___x_4219_);
                    crate::leanh::lean_ctor_set(v___x_4212_, 0, v___x_4218_);
                    v___x_4221_ = v___x_4212_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4219_);
                    v___x_4221_ = v_reuseFailAlloc_4229_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_4222_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4222_, 0, v___x_4221_);
                crate::leanh::lean_ctor_set(v___x_4222_, 1, v___x_4217_);
                v___x_4223_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_4210_, v___x_4214_);
                v___x_4224_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4224_, 0, v___x_4222_);
                crate::leanh::lean_ctor_set(v___x_4224_, 1, v___x_4223_);
                crate::leanh::lean_inc(v___y_4216_);
                v___x_4225_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4225_, 0, v___y_4216_);
                crate::leanh::lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                v___x_4226_ = 0;
                v___x_4227_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4225_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4227_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4226_,
                );
                v___x_4228_ = l_Repr_addAppParen(v___x_4227_, v_prec_4086_);
                return v___x_4228_;
            }
            21 => {
                v___x_4239_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4255_ = lean_nat_dec_le(v___x_4239_, v_prec_4086_);
                if v___x_4255_ == 0 {
                    v___x_4256_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4241_ = v___x_4256_;
                    state = 22;
                    continue;
                } else {
                    v___x_4257_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4241_ = v___x_4257_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_4242_ = crate::leanh::lean_box(1);
                v___x_4243_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__22;
                v___x_4244_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4234_, v___x_4239_);
                if v_isShared_4238_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4237_, 5);
                    crate::leanh::lean_ctor_set(v___x_4237_, 1, v___x_4244_);
                    crate::leanh::lean_ctor_set(v___x_4237_, 0, v___x_4243_);
                    v___x_4246_ = v___x_4237_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 1, v___x_4244_);
                    v___x_4246_ = v_reuseFailAlloc_4254_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4247_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4246_);
                crate::leanh::lean_ctor_set(v___x_4247_, 1, v___x_4242_);
                v___x_4248_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_4235_, v___x_4239_);
                v___x_4249_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4249_, 0, v___x_4247_);
                crate::leanh::lean_ctor_set(v___x_4249_, 1, v___x_4248_);
                crate::leanh::lean_inc(v___y_4241_);
                v___x_4250_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4250_, 0, v___y_4241_);
                crate::leanh::lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                v___x_4251_ = 0;
                v___x_4252_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4252_, 0, v___x_4250_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4251_,
                );
                v___x_4253_ = l_Repr_addAppParen(v___x_4252_, v_prec_4086_);
                return v___x_4253_;
            }
            24 => {
                v___x_4264_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4280_ = lean_nat_dec_le(v___x_4264_, v_prec_4086_);
                if v___x_4280_ == 0 {
                    v___x_4281_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4266_ = v___x_4281_;
                    state = 25;
                    continue;
                } else {
                    v___x_4282_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4266_ = v___x_4282_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_4267_ = crate::leanh::lean_box(1);
                v___x_4268_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__25;
                v___x_4269_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4259_, v___x_4264_);
                if v_isShared_4263_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4262_, 5);
                    crate::leanh::lean_ctor_set(v___x_4262_, 1, v___x_4269_);
                    crate::leanh::lean_ctor_set(v___x_4262_, 0, v___x_4268_);
                    v___x_4271_ = v___x_4262_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 1, v___x_4269_);
                    v___x_4271_ = v_reuseFailAlloc_4279_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4272_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4272_, 0, v___x_4271_);
                crate::leanh::lean_ctor_set(v___x_4272_, 1, v___x_4267_);
                v___x_4273_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_4260_, v___x_4264_);
                v___x_4274_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4274_, 0, v___x_4272_);
                crate::leanh::lean_ctor_set(v___x_4274_, 1, v___x_4273_);
                crate::leanh::lean_inc(v___y_4266_);
                v___x_4275_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4275_, 0, v___y_4266_);
                crate::leanh::lean_ctor_set(v___x_4275_, 1, v___x_4274_);
                v___x_4276_ = 0;
                v___x_4277_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4277_, 0, v___x_4275_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4276_,
                );
                v___x_4278_ = l_Repr_addAppParen(v___x_4277_, v_prec_4086_);
                return v___x_4278_;
            }
            27 => {
                v___x_4289_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4306_ = lean_nat_dec_le(v___x_4289_, v_prec_4086_);
                if v___x_4306_ == 0 {
                    v___x_4307_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4291_ = v___x_4307_;
                    state = 28;
                    continue;
                } else {
                    v___x_4308_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4291_ = v___x_4308_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4292_ = crate::leanh::lean_box(1);
                v___x_4293_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__28;
                v___x_4294_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4284_, v___x_4289_);
                if v_isShared_4288_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4287_, 5);
                    crate::leanh::lean_ctor_set(v___x_4287_, 1, v___x_4294_);
                    crate::leanh::lean_ctor_set(v___x_4287_, 0, v___x_4293_);
                    v___x_4296_ = v___x_4287_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4305_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4305_, 1, v___x_4294_);
                    v___x_4296_ = v_reuseFailAlloc_4305_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_4297_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4297_, 0, v___x_4296_);
                crate::leanh::lean_ctor_set(v___x_4297_, 1, v___x_4292_);
                v___x_4298_ = l_Nat_reprFast(v_k_4285_);
                v___x_4299_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4299_, 0, v___x_4298_);
                v___x_4300_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4300_, 0, v___x_4297_);
                crate::leanh::lean_ctor_set(v___x_4300_, 1, v___x_4299_);
                crate::leanh::lean_inc(v___y_4291_);
                v___x_4301_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4301_, 0, v___y_4291_);
                crate::leanh::lean_ctor_set(v___x_4301_, 1, v___x_4300_);
                v___x_4302_ = 0;
                v___x_4303_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4303_, 0, v___x_4301_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4303_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4302_,
                );
                v___x_4304_ = l_Repr_addAppParen(v___x_4303_, v_prec_4086_);
                return v___x_4304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprExpr_repr___boxed(
    mut v_x_4310_: *mut crate::leanh::LeanObject,
    mut v_prec_4311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4312_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_x_4310_, v_prec_4311_);
    crate::leanh::lean_dec(v_prec_4311_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote___redArg(
    mut v_ctx_4315_: *mut crate::leanh::LeanObject,
    mut v_v_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4317_ = l_Lean_RArray_getImpl___redArg(v_ctx_4315_, v_v_4316_);
    return v___x_4317_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote___redArg___boxed(
    mut v_ctx_4318_: *mut crate::leanh::LeanObject,
    mut v_v_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4320_ = l_Lean_Grind_CommRing_Var_denote___redArg(v_ctx_4318_, v_v_4319_);
    crate::leanh::lean_dec(v_v_4319_);
    crate::leanh::lean_dec_ref(v_ctx_4318_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote(
    mut v_00_u03b1_4321_: *mut crate::leanh::LeanObject,
    mut v_ctx_4322_: *mut crate::leanh::LeanObject,
    mut v_v_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4324_ = l_Lean_RArray_getImpl___redArg(v_ctx_4322_, v_v_4323_);
    return v___x_4324_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote___boxed(
    mut v_00_u03b1_4325_: *mut crate::leanh::LeanObject,
    mut v_ctx_4326_: *mut crate::leanh::LeanObject,
    mut v_v_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4328_ = l_Lean_Grind_CommRing_Var_denote(v_00_u03b1_4325_, v_ctx_4326_, v_v_4327_);
    crate::leanh::lean_dec(v_v_4327_);
    crate::leanh::lean_dec_ref(v_ctx_4326_);
    return v_res_4328_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqPower_beq(
    mut v_x_4329_: *mut crate::leanh::LeanObject,
    mut v_x_4330_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    v_x_4331_ = crate::leanh::lean_ctor_get(v_x_4329_, 0);
    v_k_4332_ = crate::leanh::lean_ctor_get(v_x_4329_, 1);
    v_x_4333_ = crate::leanh::lean_ctor_get(v_x_4330_, 0);
    v_k_4334_ = crate::leanh::lean_ctor_get(v_x_4330_, 1);
    v___x_4335_ = lean_nat_dec_eq(v_x_4331_, v_x_4333_);
    if v___x_4335_ == 0 {
        return v___x_4335_;
    } else {
        let mut v___x_4336_: u8 = 0;
        v___x_4336_ = lean_nat_dec_eq(v_k_4332_, v_k_4334_);
        return v___x_4336_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqPower_beq___boxed(
    mut v_x_4337_: *mut crate::leanh::LeanObject,
    mut v_x_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4339_: u8 = 0;
    let mut v_r_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_x_4337_, v_x_4338_);
    crate::leanh::lean_dec_ref(v_x_4338_);
    crate::leanh::lean_dec_ref(v_x_4337_);
    v_r_4340_ = crate::leanh::lean_box((v_res_4339_) as usize);
    return v_r_4340_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(
    mut v_x_4343_: *mut crate::leanh::LeanObject,
    mut v_x_4344_: *mut crate::leanh::LeanObject,
    mut v_h__1_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4346_ = crate::leanh::lean_ctor_get(v_x_4343_, 0);
    crate::leanh::lean_inc(v_x_4346_);
    v_k_4347_ = crate::leanh::lean_ctor_get(v_x_4343_, 1);
    crate::leanh::lean_inc(v_k_4347_);
    crate::leanh::lean_dec_ref(v_x_4343_);
    v_x_4348_ = crate::leanh::lean_ctor_get(v_x_4344_, 0);
    crate::leanh::lean_inc(v_x_4348_);
    v_k_4349_ = crate::leanh::lean_ctor_get(v_x_4344_, 1);
    crate::leanh::lean_inc(v_k_4349_);
    crate::leanh::lean_dec_ref(v_x_4344_);
    v___x_4350_ =
        crate::leanh::lean_apply_4(v_h__1_4345_, v_x_4346_, v_k_4347_, v_x_4348_, v_k_4349_);
    return v___x_4350_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(
    mut v_motive_4351_: *mut crate::leanh::LeanObject,
    mut v_x_4352_: *mut crate::leanh::LeanObject,
    mut v_x_4353_: *mut crate::leanh::LeanObject,
    mut v_h__1_4354_: *mut crate::leanh::LeanObject,
    mut v_h__2_4355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4356_ = crate::leanh::lean_ctor_get(v_x_4352_, 0);
    crate::leanh::lean_inc(v_x_4356_);
    v_k_4357_ = crate::leanh::lean_ctor_get(v_x_4352_, 1);
    crate::leanh::lean_inc(v_k_4357_);
    crate::leanh::lean_dec_ref(v_x_4352_);
    v_x_4358_ = crate::leanh::lean_ctor_get(v_x_4353_, 0);
    crate::leanh::lean_inc(v_x_4358_);
    v_k_4359_ = crate::leanh::lean_ctor_get(v_x_4353_, 1);
    crate::leanh::lean_inc(v_k_4359_);
    crate::leanh::lean_dec_ref(v_x_4353_);
    v___x_4360_ =
        crate::leanh::lean_apply_4(v_h__1_4354_, v_x_4356_, v_k_4357_, v_x_4358_, v_k_4359_);
    return v___x_4360_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(
    mut v_motive_4361_: *mut crate::leanh::LeanObject,
    mut v_x_4362_: *mut crate::leanh::LeanObject,
    mut v_x_4363_: *mut crate::leanh::LeanObject,
    mut v_h__1_4364_: *mut crate::leanh::LeanObject,
    mut v_h__2_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(v_motive_4361_, v_x_4362_, v_x_4363_, v_h__1_4364_, v_h__2_4365_);
    crate::leanh::lean_dec(v_h__2_4365_);
    return v_res_4366_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(
    mut v_a_4367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = lean_nat_to_int(v_a_4367_);
    return v___x_4368_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_4383_ = lean_nat_to_int(v___x_4382_);
    return v___x_4383_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4391_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0;
    v___x_4392_ = lean_string_length(v___x_4391_);
    return v___x_4392_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13,
    );
    v___x_4394_ = lean_nat_to_int(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPower_repr___redArg(
    mut v_x_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_4400_ = crate::leanh::lean_ctor_get(v_x_4399_, 0);
                v_k_4401_ = crate::leanh::lean_ctor_get(v_x_4399_, 1);
                v_isSharedCheck_4435_ = (!crate::leanh::lean_is_exclusive(v_x_4399_)) as u8;
                if v_isSharedCheck_4435_ == 0 {
                    v___x_4403_ = v_x_4399_;
                    v_isShared_4404_ = v_isSharedCheck_4435_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_k_4401_);
                    crate::leanh::lean_inc(v_x_4400_);
                    crate::leanh::lean_dec(v_x_4399_);
                    v___x_4403_ = crate::leanh::lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5;
                v___x_4406_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6;
                v___x_4407_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7,
                );
                v___x_4408_ = l_Nat_reprFast(v_x_4400_);
                v___x_4409_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4408_);
                if v_isShared_4404_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4403_, 4);
                    crate::leanh::lean_ctor_set(v___x_4403_, 1, v___x_4409_);
                    crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4407_);
                    v___x_4411_ = v___x_4403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 1, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4412_ = 0;
                v___x_4413_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4413_, 0, v___x_4411_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4413_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4412_,
                );
                v___x_4414_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4414_, 0, v___x_4406_);
                crate::leanh::lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9;
                v___x_4416_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4416_, 0, v___x_4414_);
                crate::leanh::lean_ctor_set(v___x_4416_, 1, v___x_4415_);
                v___x_4417_ = crate::leanh::lean_box(1);
                v___x_4418_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4418_, 0, v___x_4416_);
                crate::leanh::lean_ctor_set(v___x_4418_, 1, v___x_4417_);
                v___x_4419_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11;
                v___x_4420_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4420_, 0, v___x_4418_);
                crate::leanh::lean_ctor_set(v___x_4420_, 1, v___x_4419_);
                v___x_4421_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4420_);
                crate::leanh::lean_ctor_set(v___x_4421_, 1, v___x_4405_);
                v___x_4422_ = l_Nat_reprFast(v_k_4401_);
                v___x_4423_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4423_, 0, v___x_4422_);
                v___x_4424_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4424_, 0, v___x_4407_);
                crate::leanh::lean_ctor_set(v___x_4424_, 1, v___x_4423_);
                v___x_4425_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4425_, 0, v___x_4424_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4425_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4412_,
                );
                v___x_4426_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4426_, 0, v___x_4421_);
                crate::leanh::lean_ctor_set(v___x_4426_, 1, v___x_4425_);
                v___x_4427_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once
                    ),
                    _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14,
                );
                v___x_4428_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15;
                v___x_4429_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4429_, 0, v___x_4428_);
                crate::leanh::lean_ctor_set(v___x_4429_, 1, v___x_4426_);
                v___x_4430_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16;
                v___x_4431_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4431_, 0, v___x_4429_);
                crate::leanh::lean_ctor_set(v___x_4431_, 1, v___x_4430_);
                v___x_4432_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4432_, 0, v___x_4427_);
                crate::leanh::lean_ctor_set(v___x_4432_, 1, v___x_4431_);
                v___x_4433_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4433_, 0, v___x_4432_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4433_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4412_,
                );
                return v___x_4433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPower_repr(
    mut v_x_4436_: *mut crate::leanh::LeanObject,
    mut v_prec_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4438_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_x_4436_);
    return v___x_4438_;
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPower_repr___boxed(
    mut v_x_4439_: *mut crate::leanh::LeanObject,
    mut v_prec_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4441_ = l_Lean_Grind_CommRing_instReprPower_repr(v_x_4439_, v_prec_4440_);
    crate::leanh::lean_dec(v_prec_4440_);
    return v_res_4441_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePower_hash(
    mut v_x_4448_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u64 = 0;
    let mut v___x_4452_: u64 = 0;
    let mut v___x_4453_: u64 = 0;
    let mut v___x_4454_: u64 = 0;
    let mut v___x_4455_: u64 = 0;
    v_x_4449_ = crate::leanh::lean_ctor_get(v_x_4448_, 0);
    v_k_4450_ = crate::leanh::lean_ctor_get(v_x_4448_, 1);
    v___x_4451_ = 0u64;
    v___x_4452_ = lean_uint64_of_nat(v_x_4449_);
    v___x_4453_ = lean_uint64_mix_hash(v___x_4451_, v___x_4452_);
    v___x_4454_ = lean_uint64_of_nat(v_k_4450_);
    v___x_4455_ = lean_uint64_mix_hash(v___x_4453_, v___x_4454_);
    return v___x_4455_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePower_hash___boxed(
    mut v_x_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4457_: u64 = 0;
    let mut v_r_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_4456_);
    crate::leanh::lean_dec_ref(v_x_4456_);
    v_r_4458_ = crate::leanh::lean_box_uint64(v_res_4457_);
    return v_r_4458_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_varLt(
    mut v_p_u2081_4461_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_4462_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    v_x_4463_ = crate::leanh::lean_ctor_get(v_p_u2081_4461_, 0);
    v_x_4464_ = crate::leanh::lean_ctor_get(v_p_u2082_4462_, 0);
    v___x_4465_ = l_Nat_blt(v_x_4463_, v_x_4464_);
    return v___x_4465_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_varLt___boxed(
    mut v_p_u2081_4466_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_4467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4468_: u8 = 0;
    let mut v_r_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4468_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_4466_, v_p_u2082_4467_);
    crate::leanh::lean_dec_ref(v_p_u2082_4467_);
    crate::leanh::lean_dec_ref(v_p_u2081_4466_);
    v_r_4469_ = crate::leanh::lean_box((v_res_4468_) as usize);
    return v_r_4469_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote___redArg(
    mut v_inst_4470_: *mut crate::leanh::LeanObject,
    mut v_ctx_4471_: *mut crate::leanh::LeanObject,
    mut v_x_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ofNat_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    v_ofNat_4473_ = crate::leanh::lean_ctor_get(v_inst_4470_, 3);
    crate::leanh::lean_inc(v_ofNat_4473_);
    v_npow_4474_ = crate::leanh::lean_ctor_get(v_inst_4470_, 5);
    crate::leanh::lean_inc(v_npow_4474_);
    crate::leanh::lean_dec_ref(v_inst_4470_);
    v_x_4475_ = crate::leanh::lean_ctor_get(v_x_4472_, 0);
    crate::leanh::lean_inc(v_x_4475_);
    v_k_4476_ = crate::leanh::lean_ctor_get(v_x_4472_, 1);
    crate::leanh::lean_inc(v_k_4476_);
    crate::leanh::lean_dec_ref(v_x_4472_);
    v___x_4477_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4478_ = lean_nat_dec_eq(v_k_4476_, v___x_4477_);
    if v___x_4478_ == 0 {
        let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4480_: u8 = 0;
        crate::leanh::lean_dec(v_ofNat_4473_);
        v___x_4479_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4480_ = lean_nat_dec_eq(v_k_4476_, v___x_4479_);
        if v___x_4480_ == 0 {
            let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4481_ = l_Lean_RArray_getImpl___redArg(v_ctx_4471_, v_x_4475_);
            crate::leanh::lean_dec(v_x_4475_);
            v___x_4482_ = crate::leanh::lean_apply_2(v_npow_4474_, v___x_4481_, v_k_4476_);
            return v___x_4482_;
        } else {
            let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_4476_);
            crate::leanh::lean_dec(v_npow_4474_);
            v___x_4483_ = l_Lean_RArray_getImpl___redArg(v_ctx_4471_, v_x_4475_);
            crate::leanh::lean_dec(v_x_4475_);
            return v___x_4483_;
        }
    } else {
        let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_4476_);
        crate::leanh::lean_dec(v_x_4475_);
        crate::leanh::lean_dec(v_npow_4474_);
        v___x_4484_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4485_ = crate::leanh::lean_apply_1(v_ofNat_4473_, v___x_4484_);
        return v___x_4485_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote___redArg___boxed(
    mut v_inst_4486_: *mut crate::leanh::LeanObject,
    mut v_ctx_4487_: *mut crate::leanh::LeanObject,
    mut v_x_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4489_ = l_Lean_Grind_CommRing_Power_denote___redArg(v_inst_4486_, v_ctx_4487_, v_x_4488_);
    crate::leanh::lean_dec_ref(v_ctx_4487_);
    return v_res_4489_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote(
    mut v_00_u03b1_4490_: *mut crate::leanh::LeanObject,
    mut v_inst_4491_: *mut crate::leanh::LeanObject,
    mut v_ctx_4492_: *mut crate::leanh::LeanObject,
    mut v_x_4493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ofNat_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    v_ofNat_4494_ = crate::leanh::lean_ctor_get(v_inst_4491_, 3);
    crate::leanh::lean_inc(v_ofNat_4494_);
    v_npow_4495_ = crate::leanh::lean_ctor_get(v_inst_4491_, 5);
    crate::leanh::lean_inc(v_npow_4495_);
    crate::leanh::lean_dec_ref(v_inst_4491_);
    v_x_4496_ = crate::leanh::lean_ctor_get(v_x_4493_, 0);
    crate::leanh::lean_inc(v_x_4496_);
    v_k_4497_ = crate::leanh::lean_ctor_get(v_x_4493_, 1);
    crate::leanh::lean_inc(v_k_4497_);
    crate::leanh::lean_dec_ref(v_x_4493_);
    v___x_4498_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4499_ = lean_nat_dec_eq(v_k_4497_, v___x_4498_);
    if v___x_4499_ == 0 {
        let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4501_: u8 = 0;
        crate::leanh::lean_dec(v_ofNat_4494_);
        v___x_4500_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4501_ = lean_nat_dec_eq(v_k_4497_, v___x_4500_);
        if v___x_4501_ == 0 {
            let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4502_ = l_Lean_RArray_getImpl___redArg(v_ctx_4492_, v_x_4496_);
            crate::leanh::lean_dec(v_x_4496_);
            v___x_4503_ = crate::leanh::lean_apply_2(v_npow_4495_, v___x_4502_, v_k_4497_);
            return v___x_4503_;
        } else {
            let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_4497_);
            crate::leanh::lean_dec(v_npow_4495_);
            v___x_4504_ = l_Lean_RArray_getImpl___redArg(v_ctx_4492_, v_x_4496_);
            crate::leanh::lean_dec(v_x_4496_);
            return v___x_4504_;
        }
    } else {
        let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_4497_);
        crate::leanh::lean_dec(v_x_4496_);
        crate::leanh::lean_dec(v_npow_4495_);
        v___x_4505_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4506_ = crate::leanh::lean_apply_1(v_ofNat_4494_, v___x_4505_);
        return v___x_4506_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote___boxed(
    mut v_00_u03b1_4507_: *mut crate::leanh::LeanObject,
    mut v_inst_4508_: *mut crate::leanh::LeanObject,
    mut v_ctx_4509_: *mut crate::leanh::LeanObject,
    mut v_x_4510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4511_ =
        l_Lean_Grind_CommRing_Power_denote(v_00_u03b1_4507_, v_inst_4508_, v_ctx_4509_, v_x_4510_);
    crate::leanh::lean_dec_ref(v_ctx_4509_);
    return v_res_4511_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorIdx(
    mut v_x_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4512_) == 0 {
        let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4513_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4513_;
    } else {
        let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4514_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_4514_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorIdx___boxed(
    mut v_x_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_Grind_CommRing_Mon_ctorIdx(v_x_4515_);
    crate::leanh::lean_dec(v_x_4515_);
    return v_res_4516_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorElim___redArg(
    mut v_t_4517_: *mut crate::leanh::LeanObject,
    mut v_k_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4517_) == 0 {
        return v_k_4518_;
    } else {
        let mut v_p_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_4519_ = crate::leanh::lean_ctor_get(v_t_4517_, 0);
        crate::leanh::lean_inc_ref(v_p_4519_);
        v_m_4520_ = crate::leanh::lean_ctor_get(v_t_4517_, 1);
        crate::leanh::lean_inc(v_m_4520_);
        crate::leanh::lean_dec_ref_known(v_t_4517_, 2);
        v___x_4521_ = crate::leanh::lean_apply_2(v_k_4518_, v_p_4519_, v_m_4520_);
        return v___x_4521_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorElim(
    mut v_motive_4522_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4523_: *mut crate::leanh::LeanObject,
    mut v_t_4524_: *mut crate::leanh::LeanObject,
    mut v_h_4525_: *mut crate::leanh::LeanObject,
    mut v_k_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4524_, v_k_4526_);
    return v___x_4527_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorElim___boxed(
    mut v_motive_4528_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4529_: *mut crate::leanh::LeanObject,
    mut v_t_4530_: *mut crate::leanh::LeanObject,
    mut v_h_4531_: *mut crate::leanh::LeanObject,
    mut v_k_4532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4533_ = l_Lean_Grind_CommRing_Mon_ctorElim(
        v_motive_4528_,
        v_ctorIdx_4529_,
        v_t_4530_,
        v_h_4531_,
        v_k_4532_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4529_);
    return v_res_4533_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_unit_elim___redArg(
    mut v_t_4534_: *mut crate::leanh::LeanObject,
    mut v_unit_4535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4536_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4534_, v_unit_4535_);
    return v___x_4536_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_unit_elim(
    mut v_motive_4537_: *mut crate::leanh::LeanObject,
    mut v_t_4538_: *mut crate::leanh::LeanObject,
    mut v_h_4539_: *mut crate::leanh::LeanObject,
    mut v_unit_4540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4541_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4538_, v_unit_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mult_elim___redArg(
    mut v_t_4542_: *mut crate::leanh::LeanObject,
    mut v_mult_4543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4544_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4542_, v_mult_4543_);
    return v___x_4544_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mult_elim(
    mut v_motive_4545_: *mut crate::leanh::LeanObject,
    mut v_t_4546_: *mut crate::leanh::LeanObject,
    mut v_h_4547_: *mut crate::leanh::LeanObject,
    mut v_mult_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4549_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4546_, v_mult_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqMon_beq(
    mut v_x_4550_: *mut crate::leanh::LeanObject,
    mut v_x_4551_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: u8 = 0;
    let mut v_p_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4550_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_4551_) == 0 {
                        v___x_4552_ = 1;
                        return v___x_4552_;
                    } else {
                        v___x_4553_ = 0;
                        return v___x_4553_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4551_) == 1 {
                        v_p_4554_ = crate::leanh::lean_ctor_get(v_x_4550_, 0);
                        v_m_4555_ = crate::leanh::lean_ctor_get(v_x_4550_, 1);
                        v_p_4556_ = crate::leanh::lean_ctor_get(v_x_4551_, 0);
                        v_m_4557_ = crate::leanh::lean_ctor_get(v_x_4551_, 1);
                        v___x_4558_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_p_4554_, v_p_4556_);
                        if v___x_4558_ == 0 {
                            return v___x_4558_;
                        } else {
                            v_x_4550_ = v_m_4555_;
                            v_x_4551_ = v_m_4557_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_4560_ = 0;
                        return v___x_4560_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqMon_beq___boxed(
    mut v_x_4561_: *mut crate::leanh::LeanObject,
    mut v_x_4562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4563_: u8 = 0;
    let mut v_r_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4563_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_4561_, v_x_4562_);
    crate::leanh::lean_dec(v_x_4562_);
    crate::leanh::lean_dec(v_x_4561_);
    v_r_4564_ = crate::leanh::lean_box((v_res_4563_) as usize);
    return v_r_4564_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(
    mut v_x_4567_: *mut crate::leanh::LeanObject,
    mut v_x_4568_: *mut crate::leanh::LeanObject,
    mut v_h__1_4569_: *mut crate::leanh::LeanObject,
    mut v_h__2_4570_: *mut crate::leanh::LeanObject,
    mut v_h__3_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4567_) == 0 {
        crate::leanh::lean_dec(v_h__2_4570_);
        if crate::leanh::lean_obj_tag(v_x_4568_) == 0 {
            let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4571_);
            v___x_4572_ = crate::leanh::lean_box(0);
            v___x_4573_ = crate::leanh::lean_apply_1(v_h__1_4569_, v___x_4572_);
            return v___x_4573_;
        } else {
            let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_4569_);
            v___x_4574_ = crate::leanh::lean_apply_4(
                v_h__3_4571_,
                v_x_4567_,
                v_x_4568_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4574_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_4569_);
        if crate::leanh::lean_obj_tag(v_x_4568_) == 1 {
            let mut v_p_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4571_);
            v_p_4575_ = crate::leanh::lean_ctor_get(v_x_4567_, 0);
            crate::leanh::lean_inc_ref(v_p_4575_);
            v_m_4576_ = crate::leanh::lean_ctor_get(v_x_4567_, 1);
            crate::leanh::lean_inc(v_m_4576_);
            crate::leanh::lean_dec_ref_known(v_x_4567_, 2);
            v_p_4577_ = crate::leanh::lean_ctor_get(v_x_4568_, 0);
            crate::leanh::lean_inc_ref(v_p_4577_);
            v_m_4578_ = crate::leanh::lean_ctor_get(v_x_4568_, 1);
            crate::leanh::lean_inc(v_m_4578_);
            crate::leanh::lean_dec_ref_known(v_x_4568_, 2);
            v___x_4579_ = crate::leanh::lean_apply_4(
                v_h__2_4570_,
                v_p_4575_,
                v_m_4576_,
                v_p_4577_,
                v_m_4578_,
            );
            return v___x_4579_;
        } else {
            let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4570_);
            v___x_4580_ = crate::leanh::lean_apply_4(
                v_h__3_4571_,
                v_x_4567_,
                v_x_4568_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4580_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(
    mut v_motive_4581_: *mut crate::leanh::LeanObject,
    mut v_x_4582_: *mut crate::leanh::LeanObject,
    mut v_x_4583_: *mut crate::leanh::LeanObject,
    mut v_h__1_4584_: *mut crate::leanh::LeanObject,
    mut v_h__2_4585_: *mut crate::leanh::LeanObject,
    mut v_h__3_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4582_) == 0 {
        crate::leanh::lean_dec(v_h__2_4585_);
        if crate::leanh::lean_obj_tag(v_x_4583_) == 0 {
            let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4586_);
            v___x_4587_ = crate::leanh::lean_box(0);
            v___x_4588_ = crate::leanh::lean_apply_1(v_h__1_4584_, v___x_4587_);
            return v___x_4588_;
        } else {
            let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_4584_);
            v___x_4589_ = crate::leanh::lean_apply_4(
                v_h__3_4586_,
                v_x_4582_,
                v_x_4583_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4589_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_4584_);
        if crate::leanh::lean_obj_tag(v_x_4583_) == 1 {
            let mut v_p_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4586_);
            v_p_4590_ = crate::leanh::lean_ctor_get(v_x_4582_, 0);
            crate::leanh::lean_inc_ref(v_p_4590_);
            v_m_4591_ = crate::leanh::lean_ctor_get(v_x_4582_, 1);
            crate::leanh::lean_inc(v_m_4591_);
            crate::leanh::lean_dec_ref_known(v_x_4582_, 2);
            v_p_4592_ = crate::leanh::lean_ctor_get(v_x_4583_, 0);
            crate::leanh::lean_inc_ref(v_p_4592_);
            v_m_4593_ = crate::leanh::lean_ctor_get(v_x_4583_, 1);
            crate::leanh::lean_inc(v_m_4593_);
            crate::leanh::lean_dec_ref_known(v_x_4583_, 2);
            v___x_4594_ = crate::leanh::lean_apply_4(
                v_h__2_4585_,
                v_p_4590_,
                v_m_4591_,
                v_p_4592_,
                v_m_4593_,
            );
            return v___x_4594_;
        } else {
            let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4585_);
            v___x_4595_ = crate::leanh::lean_apply_4(
                v_h__3_4586_,
                v_x_4582_,
                v_x_4583_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4595_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprMon_repr(
    mut v_x_4605_: *mut crate::leanh::LeanObject,
    mut v_prec_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: u8 = 0;
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: u8 = 0;
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4605_) == 0 {
                    v___x_4614_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4615_ = lean_nat_dec_le(v___x_4614_, v_prec_4606_);
                    if v___x_4615_ == 0 {
                        v___x_4616_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                        );
                        v___y_4608_ = v___x_4616_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4617_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                            ),
                            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                        );
                        v___y_4608_ = v___x_4617_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_p_4618_ = crate::leanh::lean_ctor_get(v_x_4605_, 0);
                    v_m_4619_ = crate::leanh::lean_ctor_get(v_x_4605_, 1);
                    v_isSharedCheck_4642_ = (!crate::leanh::lean_is_exclusive(v_x_4605_)) as u8;
                    if v_isSharedCheck_4642_ == 0 {
                        v___x_4621_ = v_x_4605_;
                        v_isShared_4622_ = v_isSharedCheck_4642_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_m_4619_);
                        crate::leanh::lean_inc(v_p_4618_);
                        crate::leanh::lean_dec(v_x_4605_);
                        v___x_4621_ = crate::leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4642_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4609_ = l_Lean_Grind_CommRing_instReprMon_repr___closed__1;
                crate::leanh::lean_inc(v___y_4608_);
                v___x_4610_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4610_, 0, v___y_4608_);
                crate::leanh::lean_ctor_set(v___x_4610_, 1, v___x_4609_);
                v___x_4611_ = 0;
                v___x_4612_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4610_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4611_,
                );
                v___x_4613_ = l_Repr_addAppParen(v___x_4612_, v_prec_4606_);
                return v___x_4613_;
            }
            2 => {
                v___x_4623_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4639_ = lean_nat_dec_le(v___x_4623_, v_prec_4606_);
                if v___x_4639_ == 0 {
                    v___x_4640_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_4625_ = v___x_4640_;
                    state = 3;
                    continue;
                } else {
                    v___x_4641_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_4625_ = v___x_4641_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4626_ = crate::leanh::lean_box(1);
                v___x_4627_ = l_Lean_Grind_CommRing_instReprMon_repr___closed__4;
                v___x_4628_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_p_4618_);
                if v_isShared_4622_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4621_, 5);
                    crate::leanh::lean_ctor_set(v___x_4621_, 1, v___x_4628_);
                    crate::leanh::lean_ctor_set(v___x_4621_, 0, v___x_4627_);
                    v___x_4630_ = v___x_4621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4628_);
                    v___x_4630_ = v_reuseFailAlloc_4638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4631_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4631_, 0, v___x_4630_);
                crate::leanh::lean_ctor_set(v___x_4631_, 1, v___x_4626_);
                v___x_4632_ = l_Lean_Grind_CommRing_instReprMon_repr(v_m_4619_, v___x_4623_);
                v___x_4633_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4633_, 0, v___x_4631_);
                crate::leanh::lean_ctor_set(v___x_4633_, 1, v___x_4632_);
                crate::leanh::lean_inc(v___y_4625_);
                v___x_4634_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4634_, 0, v___y_4625_);
                crate::leanh::lean_ctor_set(v___x_4634_, 1, v___x_4633_);
                v___x_4635_ = 0;
                v___x_4636_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4636_, 0, v___x_4634_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4636_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4635_,
                );
                v___x_4637_ = l_Repr_addAppParen(v___x_4636_, v_prec_4606_);
                return v___x_4637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprMon_repr___boxed(
    mut v_x_4643_: *mut crate::leanh::LeanObject,
    mut v_prec_4644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4645_ = l_Lean_Grind_CommRing_instReprMon_repr(v_x_4643_, v_prec_4644_);
    crate::leanh::lean_dec(v_prec_4644_);
    return v_res_4645_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedMon_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4648_ = crate::leanh::lean_box(0);
    return v___x_4648_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedMon() -> *mut crate::leanh::LeanObject {
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4649_ = crate::leanh::lean_box(0);
    return v___x_4649_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableMon_hash(
    mut v_x_4650_: *mut crate::leanh::LeanObject,
) -> u64 {
    if crate::leanh::lean_obj_tag(v_x_4650_) == 0 {
        let mut v___x_4651_: u64 = 0;
        v___x_4651_ = 0u64;
        return v___x_4651_;
    } else {
        let mut v_p_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4654_: u64 = 0;
        let mut v___x_4655_: u64 = 0;
        let mut v___x_4656_: u64 = 0;
        let mut v___x_4657_: u64 = 0;
        let mut v___x_4658_: u64 = 0;
        v_p_4652_ = crate::leanh::lean_ctor_get(v_x_4650_, 0);
        v_m_4653_ = crate::leanh::lean_ctor_get(v_x_4650_, 1);
        v___x_4654_ = 1u64;
        v___x_4655_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_p_4652_);
        v___x_4656_ = lean_uint64_mix_hash(v___x_4654_, v___x_4655_);
        v___x_4657_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_m_4653_);
        v___x_4658_ = lean_uint64_mix_hash(v___x_4656_, v___x_4657_);
        return v___x_4658_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableMon_hash___boxed(
    mut v_x_4659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4660_: u64 = 0;
    let mut v_r_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4660_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_4659_);
    crate::leanh::lean_dec(v_x_4659_);
    v_r_4661_ = crate::leanh::lean_box_uint64(v_res_4660_);
    return v_r_4661_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote___redArg(
    mut v_inst_4664_: *mut crate::leanh::LeanObject,
    mut v_ctx_4665_: *mut crate::leanh::LeanObject,
    mut v_x_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ofNat_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMul_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4666_) == 0 {
                    v_ofNat_4667_ = crate::leanh::lean_ctor_get(v_inst_4664_, 3);
                    crate::leanh::lean_inc(v_ofNat_4667_);
                    crate::leanh::lean_dec_ref(v_inst_4664_);
                    v___x_4668_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4669_ = crate::leanh::lean_apply_1(v_ofNat_4667_, v___x_4668_);
                    return v___x_4669_;
                } else {
                    v_toMul_4670_ = crate::leanh::lean_ctor_get(v_inst_4664_, 1);
                    crate::leanh::lean_inc(v_toMul_4670_);
                    v_ofNat_4671_ = crate::leanh::lean_ctor_get(v_inst_4664_, 3);
                    v_npow_4672_ = crate::leanh::lean_ctor_get(v_inst_4664_, 5);
                    v_p_4673_ = crate::leanh::lean_ctor_get(v_x_4666_, 0);
                    crate::leanh::lean_inc_ref(v_p_4673_);
                    v_m_4674_ = crate::leanh::lean_ctor_get(v_x_4666_, 1);
                    crate::leanh::lean_inc(v_m_4674_);
                    crate::leanh::lean_dec_ref_known(v_x_4666_, 2);
                    v_x_4679_ = crate::leanh::lean_ctor_get(v_p_4673_, 0);
                    crate::leanh::lean_inc(v_x_4679_);
                    v_k_4680_ = crate::leanh::lean_ctor_get(v_p_4673_, 1);
                    crate::leanh::lean_inc(v_k_4680_);
                    crate::leanh::lean_dec_ref(v_p_4673_);
                    v___x_4681_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4682_ = lean_nat_dec_eq(v_k_4680_, v___x_4681_);
                    if v___x_4682_ == 0 {
                        v___x_4683_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4684_ = lean_nat_dec_eq(v_k_4680_, v___x_4683_);
                        if v___x_4684_ == 0 {
                            v___x_4685_ = l_Lean_RArray_getImpl___redArg(v_ctx_4665_, v_x_4679_);
                            crate::leanh::lean_dec(v_x_4679_);
                            crate::leanh::lean_inc(v_npow_4672_);
                            v___x_4686_ =
                                crate::leanh::lean_apply_2(v_npow_4672_, v___x_4685_, v_k_4680_);
                            v___y_4676_ = v___x_4686_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_k_4680_);
                            v___x_4687_ = l_Lean_RArray_getImpl___redArg(v_ctx_4665_, v_x_4679_);
                            crate::leanh::lean_dec(v_x_4679_);
                            v___y_4676_ = v___x_4687_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_4680_);
                        crate::leanh::lean_dec(v_x_4679_);
                        v___x_4688_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v_ofNat_4671_);
                        v___x_4689_ = crate::leanh::lean_apply_1(v_ofNat_4671_, v___x_4688_);
                        v___y_4676_ = v___x_4689_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4677_ =
                    l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_4664_, v_ctx_4665_, v_m_4674_);
                v___x_4678_ = crate::leanh::lean_apply_2(v_toMul_4670_, v___y_4676_, v___x_4677_);
                return v___x_4678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(
    mut v_inst_4690_: *mut crate::leanh::LeanObject,
    mut v_ctx_4691_: *mut crate::leanh::LeanObject,
    mut v_x_4692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4693_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_4690_, v_ctx_4691_, v_x_4692_);
    crate::leanh::lean_dec_ref(v_ctx_4691_);
    return v_res_4693_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote(
    mut v_00_u03b1_4694_: *mut crate::leanh::LeanObject,
    mut v_inst_4695_: *mut crate::leanh::LeanObject,
    mut v_ctx_4696_: *mut crate::leanh::LeanObject,
    mut v_x_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_4695_, v_ctx_4696_, v_x_4697_);
    return v___x_4698_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote___boxed(
    mut v_00_u03b1_4699_: *mut crate::leanh::LeanObject,
    mut v_inst_4700_: *mut crate::leanh::LeanObject,
    mut v_ctx_4701_: *mut crate::leanh::LeanObject,
    mut v_x_4702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4703_ =
        l_Lean_Grind_CommRing_Mon_denote(v_00_u03b1_4699_, v_inst_4700_, v_ctx_4701_, v_x_4702_);
    crate::leanh::lean_dec_ref(v_ctx_4701_);
    return v_res_4703_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
    mut v_inst_4704_: *mut crate::leanh::LeanObject,
    mut v_ctx_4705_: *mut crate::leanh::LeanObject,
    mut v_m_4706_: *mut crate::leanh::LeanObject,
    mut v_acc_4707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMul_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: u8 = 0;
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_4706_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_4704_);
                    return v_acc_4707_;
                } else {
                    v_toMul_4708_ = crate::leanh::lean_ctor_get(v_inst_4704_, 1);
                    v_ofNat_4709_ = crate::leanh::lean_ctor_get(v_inst_4704_, 3);
                    v_npow_4710_ = crate::leanh::lean_ctor_get(v_inst_4704_, 5);
                    v_p_4711_ = crate::leanh::lean_ctor_get(v_m_4706_, 0);
                    crate::leanh::lean_inc_ref(v_p_4711_);
                    v_m_4712_ = crate::leanh::lean_ctor_get(v_m_4706_, 1);
                    crate::leanh::lean_inc(v_m_4712_);
                    crate::leanh::lean_dec_ref_known(v_m_4706_, 2);
                    v_x_4717_ = crate::leanh::lean_ctor_get(v_p_4711_, 0);
                    crate::leanh::lean_inc(v_x_4717_);
                    v_k_4718_ = crate::leanh::lean_ctor_get(v_p_4711_, 1);
                    crate::leanh::lean_inc(v_k_4718_);
                    crate::leanh::lean_dec_ref(v_p_4711_);
                    v___x_4719_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4720_ = lean_nat_dec_eq(v_k_4718_, v___x_4719_);
                    if v___x_4720_ == 0 {
                        v___x_4721_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4722_ = lean_nat_dec_eq(v_k_4718_, v___x_4721_);
                        if v___x_4722_ == 0 {
                            v___x_4723_ = l_Lean_RArray_getImpl___redArg(v_ctx_4705_, v_x_4717_);
                            crate::leanh::lean_dec(v_x_4717_);
                            crate::leanh::lean_inc(v_npow_4710_);
                            v___x_4724_ =
                                crate::leanh::lean_apply_2(v_npow_4710_, v___x_4723_, v_k_4718_);
                            v___y_4714_ = v___x_4724_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_k_4718_);
                            v___x_4725_ = l_Lean_RArray_getImpl___redArg(v_ctx_4705_, v_x_4717_);
                            crate::leanh::lean_dec(v_x_4717_);
                            v___y_4714_ = v___x_4725_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_4718_);
                        crate::leanh::lean_dec(v_x_4717_);
                        v___x_4726_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v_ofNat_4709_);
                        v___x_4727_ = crate::leanh::lean_apply_1(v_ofNat_4709_, v___x_4726_);
                        v___y_4714_ = v___x_4727_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toMul_4708_);
                v___x_4715_ = crate::leanh::lean_apply_2(v_toMul_4708_, v_acc_4707_, v___y_4714_);
                v_m_4706_ = v_m_4712_;
                v_acc_4707_ = v___x_4715_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(
    mut v_inst_4728_: *mut crate::leanh::LeanObject,
    mut v_ctx_4729_: *mut crate::leanh::LeanObject,
    mut v_m_4730_: *mut crate::leanh::LeanObject,
    mut v_acc_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4732_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
        v_inst_4728_,
        v_ctx_4729_,
        v_m_4730_,
        v_acc_4731_,
    );
    crate::leanh::lean_dec_ref(v_ctx_4729_);
    return v_res_4732_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go(
    mut v_00_u03b1_4733_: *mut crate::leanh::LeanObject,
    mut v_inst_4734_: *mut crate::leanh::LeanObject,
    mut v_ctx_4735_: *mut crate::leanh::LeanObject,
    mut v_m_4736_: *mut crate::leanh::LeanObject,
    mut v_acc_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
        v_inst_4734_,
        v_ctx_4735_,
        v_m_4736_,
        v_acc_4737_,
    );
    return v___x_4738_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(
    mut v_00_u03b1_4739_: *mut crate::leanh::LeanObject,
    mut v_inst_4740_: *mut crate::leanh::LeanObject,
    mut v_ctx_4741_: *mut crate::leanh::LeanObject,
    mut v_m_4742_: *mut crate::leanh::LeanObject,
    mut v_acc_4743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4744_ = l_Lean_Grind_CommRing_Mon_denote_x27_go(
        v_00_u03b1_4739_,
        v_inst_4740_,
        v_ctx_4741_,
        v_m_4742_,
        v_acc_4743_,
    );
    crate::leanh::lean_dec_ref(v_ctx_4741_);
    return v_res_4744_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27___redArg(
    mut v_inst_4745_: *mut crate::leanh::LeanObject,
    mut v_ctx_4746_: *mut crate::leanh::LeanObject,
    mut v_m_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_4747_) == 0 {
        let mut v_ofNat_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ofNat_4748_ = crate::leanh::lean_ctor_get(v_inst_4745_, 3);
        crate::leanh::lean_inc(v_ofNat_4748_);
        crate::leanh::lean_dec_ref(v_inst_4745_);
        v___x_4749_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4750_ = crate::leanh::lean_apply_1(v_ofNat_4748_, v___x_4749_);
        return v___x_4750_;
    } else {
        let mut v_p_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_npow_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4758_: u8 = 0;
        v_p_4751_ = crate::leanh::lean_ctor_get(v_m_4747_, 0);
        crate::leanh::lean_inc_ref(v_p_4751_);
        v_m_4752_ = crate::leanh::lean_ctor_get(v_m_4747_, 1);
        crate::leanh::lean_inc(v_m_4752_);
        crate::leanh::lean_dec_ref_known(v_m_4747_, 2);
        v_ofNat_4753_ = crate::leanh::lean_ctor_get(v_inst_4745_, 3);
        v_npow_4754_ = crate::leanh::lean_ctor_get(v_inst_4745_, 5);
        v_x_4755_ = crate::leanh::lean_ctor_get(v_p_4751_, 0);
        crate::leanh::lean_inc(v_x_4755_);
        v_k_4756_ = crate::leanh::lean_ctor_get(v_p_4751_, 1);
        crate::leanh::lean_inc(v_k_4756_);
        crate::leanh::lean_dec_ref(v_p_4751_);
        v___x_4757_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4758_ = lean_nat_dec_eq(v_k_4756_, v___x_4757_);
        if v___x_4758_ == 0 {
            let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4760_: u8 = 0;
            v___x_4759_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4760_ = lean_nat_dec_eq(v_k_4756_, v___x_4759_);
            if v___x_4760_ == 0 {
                let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4761_ = l_Lean_RArray_getImpl___redArg(v_ctx_4746_, v_x_4755_);
                crate::leanh::lean_dec(v_x_4755_);
                crate::leanh::lean_inc(v_npow_4754_);
                v___x_4762_ = crate::leanh::lean_apply_2(v_npow_4754_, v___x_4761_, v_k_4756_);
                v___x_4763_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4745_,
                    v_ctx_4746_,
                    v_m_4752_,
                    v___x_4762_,
                );
                return v___x_4763_;
            } else {
                let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_4756_);
                v___x_4764_ = l_Lean_RArray_getImpl___redArg(v_ctx_4746_, v_x_4755_);
                crate::leanh::lean_dec(v_x_4755_);
                v___x_4765_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4745_,
                    v_ctx_4746_,
                    v_m_4752_,
                    v___x_4764_,
                );
                return v___x_4765_;
            }
        } else {
            let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_4756_);
            crate::leanh::lean_dec(v_x_4755_);
            v___x_4766_ = crate::leanh::lean_unsigned_to_nat(1);
            crate::leanh::lean_inc(v_ofNat_4753_);
            v___x_4767_ = crate::leanh::lean_apply_1(v_ofNat_4753_, v___x_4766_);
            v___x_4768_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                v_inst_4745_,
                v_ctx_4746_,
                v_m_4752_,
                v___x_4767_,
            );
            return v___x_4768_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(
    mut v_inst_4769_: *mut crate::leanh::LeanObject,
    mut v_ctx_4770_: *mut crate::leanh::LeanObject,
    mut v_m_4771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4772_ =
        l_Lean_Grind_CommRing_Mon_denote_x27___redArg(v_inst_4769_, v_ctx_4770_, v_m_4771_);
    crate::leanh::lean_dec_ref(v_ctx_4770_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27(
    mut v_00_u03b1_4773_: *mut crate::leanh::LeanObject,
    mut v_inst_4774_: *mut crate::leanh::LeanObject,
    mut v_ctx_4775_: *mut crate::leanh::LeanObject,
    mut v_m_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_4776_) == 0 {
        let mut v_ofNat_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ofNat_4777_ = crate::leanh::lean_ctor_get(v_inst_4774_, 3);
        crate::leanh::lean_inc(v_ofNat_4777_);
        crate::leanh::lean_dec_ref(v_inst_4774_);
        v___x_4778_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4779_ = crate::leanh::lean_apply_1(v_ofNat_4777_, v___x_4778_);
        return v___x_4779_;
    } else {
        let mut v_p_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_npow_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4787_: u8 = 0;
        v_p_4780_ = crate::leanh::lean_ctor_get(v_m_4776_, 0);
        crate::leanh::lean_inc_ref(v_p_4780_);
        v_m_4781_ = crate::leanh::lean_ctor_get(v_m_4776_, 1);
        crate::leanh::lean_inc(v_m_4781_);
        crate::leanh::lean_dec_ref_known(v_m_4776_, 2);
        v_ofNat_4782_ = crate::leanh::lean_ctor_get(v_inst_4774_, 3);
        v_npow_4783_ = crate::leanh::lean_ctor_get(v_inst_4774_, 5);
        v_x_4784_ = crate::leanh::lean_ctor_get(v_p_4780_, 0);
        crate::leanh::lean_inc(v_x_4784_);
        v_k_4785_ = crate::leanh::lean_ctor_get(v_p_4780_, 1);
        crate::leanh::lean_inc(v_k_4785_);
        crate::leanh::lean_dec_ref(v_p_4780_);
        v___x_4786_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4787_ = lean_nat_dec_eq(v_k_4785_, v___x_4786_);
        if v___x_4787_ == 0 {
            let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4789_: u8 = 0;
            v___x_4788_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4789_ = lean_nat_dec_eq(v_k_4785_, v___x_4788_);
            if v___x_4789_ == 0 {
                let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4790_ = l_Lean_RArray_getImpl___redArg(v_ctx_4775_, v_x_4784_);
                crate::leanh::lean_dec(v_x_4784_);
                crate::leanh::lean_inc(v_npow_4783_);
                v___x_4791_ = crate::leanh::lean_apply_2(v_npow_4783_, v___x_4790_, v_k_4785_);
                v___x_4792_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4774_,
                    v_ctx_4775_,
                    v_m_4781_,
                    v___x_4791_,
                );
                return v___x_4792_;
            } else {
                let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_4785_);
                v___x_4793_ = l_Lean_RArray_getImpl___redArg(v_ctx_4775_, v_x_4784_);
                crate::leanh::lean_dec(v_x_4784_);
                v___x_4794_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4774_,
                    v_ctx_4775_,
                    v_m_4781_,
                    v___x_4793_,
                );
                return v___x_4794_;
            }
        } else {
            let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_4785_);
            crate::leanh::lean_dec(v_x_4784_);
            v___x_4795_ = crate::leanh::lean_unsigned_to_nat(1);
            crate::leanh::lean_inc(v_ofNat_4782_);
            v___x_4796_ = crate::leanh::lean_apply_1(v_ofNat_4782_, v___x_4795_);
            v___x_4797_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                v_inst_4774_,
                v_ctx_4775_,
                v_m_4781_,
                v___x_4796_,
            );
            return v___x_4797_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27___boxed(
    mut v_00_u03b1_4798_: *mut crate::leanh::LeanObject,
    mut v_inst_4799_: *mut crate::leanh::LeanObject,
    mut v_ctx_4800_: *mut crate::leanh::LeanObject,
    mut v_m_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lean_Grind_CommRing_Mon_denote_x27(
        v_00_u03b1_4798_,
        v_inst_4799_,
        v_ctx_4800_,
        v_m_4801_,
    );
    crate::leanh::lean_dec_ref(v_ctx_4800_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ofVar(
    mut v_x_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4805_, 0, v_x_4803_);
    crate::leanh::lean_ctor_set(v___x_4805_, 1, v___x_4804_);
    v___x_4806_ = crate::leanh::lean_box(0);
    v___x_4807_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4807_, 0, v___x_4805_);
    crate::leanh::lean_ctor_set(v___x_4807_, 1, v___x_4806_);
    return v___x_4807_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_concat(
    mut v_m_u2081_4808_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4814_: u8 = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_u2081_4808_) == 0 {
                    crate::leanh::lean_inc(v_m_u2082_4809_);
                    return v_m_u2082_4809_;
                } else {
                    v_p_4810_ = crate::leanh::lean_ctor_get(v_m_u2081_4808_, 0);
                    v_m_4811_ = crate::leanh::lean_ctor_get(v_m_u2081_4808_, 1);
                    v_isSharedCheck_4819_ =
                        (!crate::leanh::lean_is_exclusive(v_m_u2081_4808_)) as u8;
                    if v_isSharedCheck_4819_ == 0 {
                        v___x_4813_ = v_m_u2081_4808_;
                        v_isShared_4814_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_m_4811_);
                        crate::leanh::lean_inc(v_p_4810_);
                        crate::leanh::lean_dec(v_m_u2081_4808_);
                        v___x_4813_ = crate::leanh::lean_box(0);
                        v_isShared_4814_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4815_ = l_Lean_Grind_CommRing_Mon_concat(v_m_4811_, v_m_u2082_4809_);
                if v_isShared_4814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4813_, 1, v___x_4815_);
                    v___x_4817_ = v___x_4813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4818_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_p_4810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 1, v___x_4815_);
                    v___x_4817_ = v_reuseFailAlloc_4818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_concat___boxed(
    mut v_m_u2081_4820_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_4820_, v_m_u2082_4821_);
    crate::leanh::lean_dec(v_m_u2082_4821_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mulPow(
    mut v_pw_4823_: *mut crate::leanh::LeanObject,
    mut v_m_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: u8 = 0;
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4831_: u8 = 0;
    let mut v___x_4832_: u8 = 0;
    let mut v_x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut v_unused_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4852_: u8 = 0;
    let mut v_unused_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_4824_) == 0 {
                    v___x_4825_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4825_, 0, v_pw_4823_);
                    crate::leanh::lean_ctor_set(v___x_4825_, 1, v_m_4824_);
                    return v___x_4825_;
                } else {
                    v_p_4826_ = crate::leanh::lean_ctor_get(v_m_4824_, 0);
                    crate::leanh::lean_inc_ref(v_p_4826_);
                    v_m_4827_ = crate::leanh::lean_ctor_get(v_m_4824_, 1);
                    v___x_4828_ = l_Lean_Grind_CommRing_Power_varLt(v_pw_4823_, v_p_4826_);
                    if v___x_4828_ == 0 {
                        crate::leanh::lean_inc(v_m_4827_);
                        v_isSharedCheck_4852_ = (!crate::leanh::lean_is_exclusive(v_m_4824_)) as u8;
                        if v_isSharedCheck_4852_ == 0 {
                            v_unused_4853_ = crate::leanh::lean_ctor_get(v_m_4824_, 1);
                            crate::leanh::lean_dec(v_unused_4853_);
                            v_unused_4854_ = crate::leanh::lean_ctor_get(v_m_4824_, 0);
                            crate::leanh::lean_dec(v_unused_4854_);
                            v___x_4830_ = v_m_4824_;
                            v_isShared_4831_ = v_isSharedCheck_4852_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_4824_);
                            v___x_4830_ = crate::leanh::lean_box(0);
                            v_isShared_4831_ = v_isSharedCheck_4852_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_4826_);
                        v___x_4855_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4855_, 0, v_pw_4823_);
                        crate::leanh::lean_ctor_set(v___x_4855_, 1, v_m_4824_);
                        return v___x_4855_;
                    }
                }
            }
            1 => {
                v___x_4832_ = l_Lean_Grind_CommRing_Power_varLt(v_p_4826_, v_pw_4823_);
                if v___x_4832_ == 0 {
                    v_x_4833_ = crate::leanh::lean_ctor_get(v_pw_4823_, 0);
                    crate::leanh::lean_inc(v_x_4833_);
                    v_k_4834_ = crate::leanh::lean_ctor_get(v_pw_4823_, 1);
                    crate::leanh::lean_inc(v_k_4834_);
                    crate::leanh::lean_dec_ref(v_pw_4823_);
                    v_k_4835_ = crate::leanh::lean_ctor_get(v_p_4826_, 1);
                    v_isSharedCheck_4846_ = (!crate::leanh::lean_is_exclusive(v_p_4826_)) as u8;
                    if v_isSharedCheck_4846_ == 0 {
                        v_unused_4847_ = crate::leanh::lean_ctor_get(v_p_4826_, 0);
                        crate::leanh::lean_dec(v_unused_4847_);
                        v___x_4837_ = v_p_4826_;
                        v_isShared_4838_ = v_isSharedCheck_4846_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4835_);
                        crate::leanh::lean_dec(v_p_4826_);
                        v___x_4837_ = crate::leanh::lean_box(0);
                        v_isShared_4838_ = v_isSharedCheck_4846_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4848_ = l_Lean_Grind_CommRing_Mon_mulPow(v_pw_4823_, v_m_4827_);
                    if v_isShared_4831_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4830_, 1, v___x_4848_);
                        v___x_4850_ = v___x_4830_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4851_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_p_4826_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4851_, 1, v___x_4848_);
                        v___x_4850_ = v_reuseFailAlloc_4851_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4839_ = lean_nat_add(v_k_4834_, v_k_4835_);
                crate::leanh::lean_dec(v_k_4835_);
                crate::leanh::lean_dec(v_k_4834_);
                if v_isShared_4838_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4837_, 1, v___x_4839_);
                    crate::leanh::lean_ctor_set(v___x_4837_, 0, v_x_4833_);
                    v___x_4841_ = v___x_4837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_x_4833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 1, v___x_4839_);
                    v___x_4841_ = v_reuseFailAlloc_4845_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4830_, 0, v___x_4841_);
                    v___x_4843_ = v___x_4830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4844_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4844_, 1, v_m_4827_);
                    v___x_4843_ = v_reuseFailAlloc_4844_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4843_;
            }
            5 => {
                return v___x_4850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mulPow__nc(
    mut v_pw_4856_: *mut crate::leanh::LeanObject,
    mut v_m_4857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4868_: u8 = 0;
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_unused_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_4857_) == 0 {
                    v___x_4858_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4858_, 0, v_pw_4856_);
                    crate::leanh::lean_ctor_set(v___x_4858_, 1, v_m_4857_);
                    return v___x_4858_;
                } else {
                    v_p_4859_ = crate::leanh::lean_ctor_get(v_m_4857_, 0);
                    crate::leanh::lean_inc_ref(v_p_4859_);
                    v_m_4860_ = crate::leanh::lean_ctor_get(v_m_4857_, 1);
                    v_x_4861_ = crate::leanh::lean_ctor_get(v_pw_4856_, 0);
                    v_k_4862_ = crate::leanh::lean_ctor_get(v_pw_4856_, 1);
                    v_x_4863_ = crate::leanh::lean_ctor_get(v_p_4859_, 0);
                    v_k_4864_ = crate::leanh::lean_ctor_get(v_p_4859_, 1);
                    v_isSharedCheck_4883_ = (!crate::leanh::lean_is_exclusive(v_p_4859_)) as u8;
                    if v_isSharedCheck_4883_ == 0 {
                        v___x_4866_ = v_p_4859_;
                        v_isShared_4867_ = v_isSharedCheck_4883_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4864_);
                        crate::leanh::lean_inc(v_x_4863_);
                        crate::leanh::lean_dec(v_p_4859_);
                        v___x_4866_ = crate::leanh::lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4868_ = lean_nat_dec_eq(v_x_4861_, v_x_4863_);
                crate::leanh::lean_dec(v_x_4863_);
                if v___x_4868_ == 0 {
                    crate::leanh::lean_del_object(v___x_4866_);
                    crate::leanh::lean_dec(v_k_4864_);
                    v___x_4869_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4869_, 0, v_pw_4856_);
                    crate::leanh::lean_ctor_set(v___x_4869_, 1, v_m_4857_);
                    return v___x_4869_;
                } else {
                    crate::leanh::lean_inc(v_k_4862_);
                    crate::leanh::lean_inc(v_x_4861_);
                    crate::leanh::lean_inc(v_m_4860_);
                    crate::leanh::lean_dec_ref(v_pw_4856_);
                    v_isSharedCheck_4880_ = (!crate::leanh::lean_is_exclusive(v_m_4857_)) as u8;
                    if v_isSharedCheck_4880_ == 0 {
                        v_unused_4881_ = crate::leanh::lean_ctor_get(v_m_4857_, 1);
                        crate::leanh::lean_dec(v_unused_4881_);
                        v_unused_4882_ = crate::leanh::lean_ctor_get(v_m_4857_, 0);
                        crate::leanh::lean_dec(v_unused_4882_);
                        v___x_4871_ = v_m_4857_;
                        v_isShared_4872_ = v_isSharedCheck_4880_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4857_);
                        v___x_4871_ = crate::leanh::lean_box(0);
                        v_isShared_4872_ = v_isSharedCheck_4880_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4873_ = lean_nat_add(v_k_4862_, v_k_4864_);
                crate::leanh::lean_dec(v_k_4864_);
                crate::leanh::lean_dec(v_k_4862_);
                if v_isShared_4867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4866_, 1, v___x_4873_);
                    crate::leanh::lean_ctor_set(v___x_4866_, 0, v_x_4861_);
                    v___x_4875_ = v___x_4866_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_x_4861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4879_, 1, v___x_4873_);
                    v___x_4875_ = v_reuseFailAlloc_4879_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4871_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 1, v_m_4860_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_length(
    mut v_x_4884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4884_) == 0 {
        let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4885_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4885_;
    } else {
        let mut v_m_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_m_4886_ = crate::leanh::lean_ctor_get(v_x_4884_, 1);
        v___x_4887_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4888_ = l_Lean_Grind_CommRing_Mon_length(v_m_4886_);
        v___x_4889_ = lean_nat_add(v___x_4887_, v___x_4888_);
        crate::leanh::lean_dec(v___x_4888_);
        return v___x_4889_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_length___boxed(
    mut v_x_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_Lean_Grind_CommRing_Mon_length(v_x_4890_);
    crate::leanh::lean_dec(v_x_4890_);
    return v_res_4891_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_hugeFuel() -> *mut crate::leanh::LeanObject {
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4892_ = crate::leanh::lean_unsigned_to_nat(1000000);
    return v___x_4892_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul_go(
    mut v_fuel_4893_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4894_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4897_: u8 = 0;
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: u8 = 0;
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4909_: u8 = 0;
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v_x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v_unused_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4929_: u8 = 0;
    let mut v_unused_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut v_unused_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_unused_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4896_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4897_ = lean_nat_dec_eq(v_fuel_4893_, v_zero_4896_);
                if v_isZero_4897_ == 1 {
                    v___x_4898_ =
                        l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_4894_, v_m_u2082_4895_);
                    crate::leanh::lean_dec(v_m_u2082_4895_);
                    return v___x_4898_;
                } else {
                    if crate::leanh::lean_obj_tag(v_m_u2082_4895_) == 0 {
                        return v_m_u2081_4894_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_m_u2081_4894_) == 0 {
                            return v_m_u2082_4895_;
                        } else {
                            v_p_4899_ = crate::leanh::lean_ctor_get(v_m_u2082_4895_, 0);
                            crate::leanh::lean_inc_ref(v_p_4899_);
                            v_m_4900_ = crate::leanh::lean_ctor_get(v_m_u2082_4895_, 1);
                            v_p_4901_ = crate::leanh::lean_ctor_get(v_m_u2081_4894_, 0);
                            v_m_4902_ = crate::leanh::lean_ctor_get(v_m_u2081_4894_, 1);
                            v_one_4903_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_n_4904_ = lean_nat_sub(v_fuel_4893_, v_one_4903_);
                            v___x_4905_ = l_Lean_Grind_CommRing_Power_varLt(v_p_4901_, v_p_4899_);
                            if v___x_4905_ == 0 {
                                crate::leanh::lean_inc(v_m_4900_);
                                v_isSharedCheck_4936_ =
                                    (!crate::leanh::lean_is_exclusive(v_m_u2082_4895_)) as u8;
                                if v_isSharedCheck_4936_ == 0 {
                                    v_unused_4937_ =
                                        crate::leanh::lean_ctor_get(v_m_u2082_4895_, 1);
                                    crate::leanh::lean_dec(v_unused_4937_);
                                    v_unused_4938_ =
                                        crate::leanh::lean_ctor_get(v_m_u2082_4895_, 0);
                                    crate::leanh::lean_dec(v_unused_4938_);
                                    v___x_4907_ = v_m_u2082_4895_;
                                    v_isShared_4908_ = v_isSharedCheck_4936_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_m_u2082_4895_);
                                    v___x_4907_ = crate::leanh::lean_box(0);
                                    v_isShared_4908_ = v_isSharedCheck_4936_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_m_4902_);
                                crate::leanh::lean_inc_ref(v_p_4901_);
                                crate::leanh::lean_dec_ref(v_p_4899_);
                                v_isSharedCheck_4946_ =
                                    (!crate::leanh::lean_is_exclusive(v_m_u2081_4894_)) as u8;
                                if v_isSharedCheck_4946_ == 0 {
                                    v_unused_4947_ =
                                        crate::leanh::lean_ctor_get(v_m_u2081_4894_, 1);
                                    crate::leanh::lean_dec(v_unused_4947_);
                                    v_unused_4948_ =
                                        crate::leanh::lean_ctor_get(v_m_u2081_4894_, 0);
                                    crate::leanh::lean_dec(v_unused_4948_);
                                    v___x_4940_ = v_m_u2081_4894_;
                                    v_isShared_4941_ = v_isSharedCheck_4946_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_m_u2081_4894_);
                                    v___x_4940_ = crate::leanh::lean_box(0);
                                    v_isShared_4941_ = v_isSharedCheck_4946_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4909_ = l_Lean_Grind_CommRing_Power_varLt(v_p_4899_, v_p_4901_);
                if v___x_4909_ == 0 {
                    crate::leanh::lean_inc(v_m_4902_);
                    crate::leanh::lean_inc_ref(v_p_4901_);
                    crate::leanh::lean_del_object(v___x_4907_);
                    v_isSharedCheck_4929_ =
                        (!crate::leanh::lean_is_exclusive(v_m_u2081_4894_)) as u8;
                    if v_isSharedCheck_4929_ == 0 {
                        v_unused_4930_ = crate::leanh::lean_ctor_get(v_m_u2081_4894_, 1);
                        crate::leanh::lean_dec(v_unused_4930_);
                        v_unused_4931_ = crate::leanh::lean_ctor_get(v_m_u2081_4894_, 0);
                        crate::leanh::lean_dec(v_unused_4931_);
                        v___x_4911_ = v_m_u2081_4894_;
                        v_isShared_4912_ = v_isSharedCheck_4929_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_u2081_4894_);
                        v___x_4911_ = crate::leanh::lean_box(0);
                        v_isShared_4912_ = v_isSharedCheck_4929_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4932_ =
                        l_Lean_Grind_CommRing_Mon_mul_go(v_n_4904_, v_m_u2081_4894_, v_m_4900_);
                    crate::leanh::lean_dec(v_n_4904_);
                    if v_isShared_4908_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4907_, 1, v___x_4932_);
                        v___x_4934_ = v___x_4907_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4935_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_p_4899_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4935_, 1, v___x_4932_);
                        v___x_4934_ = v_reuseFailAlloc_4935_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4913_ = crate::leanh::lean_ctor_get(v_p_4901_, 0);
                crate::leanh::lean_inc(v_x_4913_);
                v_k_4914_ = crate::leanh::lean_ctor_get(v_p_4901_, 1);
                crate::leanh::lean_inc(v_k_4914_);
                crate::leanh::lean_dec_ref(v_p_4901_);
                v_k_4915_ = crate::leanh::lean_ctor_get(v_p_4899_, 1);
                v_isSharedCheck_4927_ = (!crate::leanh::lean_is_exclusive(v_p_4899_)) as u8;
                if v_isSharedCheck_4927_ == 0 {
                    v_unused_4928_ = crate::leanh::lean_ctor_get(v_p_4899_, 0);
                    crate::leanh::lean_dec(v_unused_4928_);
                    v___x_4917_ = v_p_4899_;
                    v_isShared_4918_ = v_isSharedCheck_4927_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_k_4915_);
                    crate::leanh::lean_dec(v_p_4899_);
                    v___x_4917_ = crate::leanh::lean_box(0);
                    v_isShared_4918_ = v_isSharedCheck_4927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4919_ = lean_nat_add(v_k_4914_, v_k_4915_);
                crate::leanh::lean_dec(v_k_4915_);
                crate::leanh::lean_dec(v_k_4914_);
                if v_isShared_4918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4917_, 1, v___x_4919_);
                    crate::leanh::lean_ctor_set(v___x_4917_, 0, v_x_4913_);
                    v___x_4921_ = v___x_4917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_x_4913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 1, v___x_4919_);
                    v___x_4921_ = v_reuseFailAlloc_4926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4922_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_4904_, v_m_4902_, v_m_4900_);
                crate::leanh::lean_dec(v_n_4904_);
                if v_isShared_4912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4911_, 1, v___x_4922_);
                    crate::leanh::lean_ctor_set(v___x_4911_, 0, v___x_4921_);
                    v___x_4924_ = v___x_4911_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4925_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 1, v___x_4922_);
                    v___x_4924_ = v_reuseFailAlloc_4925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4924_;
            }
            6 => {
                return v___x_4934_;
            }
            7 => {
                v___x_4942_ =
                    l_Lean_Grind_CommRing_Mon_mul_go(v_n_4904_, v_m_4902_, v_m_u2082_4895_);
                crate::leanh::lean_dec(v_n_4904_);
                if v_isShared_4941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4940_, 1, v___x_4942_);
                    v___x_4944_ = v___x_4940_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_p_4901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 1, v___x_4942_);
                    v___x_4944_ = v_reuseFailAlloc_4945_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul_go___boxed(
    mut v_fuel_4949_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4950_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4952_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_4949_, v_m_u2081_4950_, v_m_u2082_4951_);
    crate::leanh::lean_dec(v_fuel_4949_);
    return v_res_4952_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul(
    mut v_m_u2081_4953_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_4956_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_4955_, v_m_u2081_4953_, v_m_u2082_4954_);
    return v___x_4956_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(
    mut v_fuel_4957_: *mut crate::leanh::LeanObject,
    mut v_h__1_4958_: *mut crate::leanh::LeanObject,
    mut v_h__2_4959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4961_: u8 = 0;
    v_zero_4960_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_4961_ = lean_nat_dec_eq(v_fuel_4957_, v_zero_4960_);
    if v_isZero_4961_ == 1 {
        let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4959_);
        v___x_4962_ = crate::leanh::lean_box(0);
        v___x_4963_ = crate::leanh::lean_apply_1(v_h__1_4958_, v___x_4962_);
        return v___x_4963_;
    } else {
        let mut v_one_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4958_);
        v_one_4964_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_4965_ = lean_nat_sub(v_fuel_4957_, v_one_4964_);
        v___x_4966_ = crate::leanh::lean_apply_1(v_h__2_4959_, v_n_4965_);
        return v___x_4966_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(
    mut v_fuel_4967_: *mut crate::leanh::LeanObject,
    mut v_h__1_4968_: *mut crate::leanh::LeanObject,
    mut v_h__2_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_4967_, v_h__1_4968_, v_h__2_4969_);
    crate::leanh::lean_dec(v_fuel_4967_);
    return v_res_4970_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(
    mut v_motive_4971_: *mut crate::leanh::LeanObject,
    mut v_fuel_4972_: *mut crate::leanh::LeanObject,
    mut v_h__1_4973_: *mut crate::leanh::LeanObject,
    mut v_h__2_4974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4976_: u8 = 0;
    v_zero_4975_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_4976_ = lean_nat_dec_eq(v_fuel_4972_, v_zero_4975_);
    if v_isZero_4976_ == 1 {
        let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4974_);
        v___x_4977_ = crate::leanh::lean_box(0);
        v___x_4978_ = crate::leanh::lean_apply_1(v_h__1_4973_, v___x_4977_);
        return v___x_4978_;
    } else {
        let mut v_one_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4973_);
        v_one_4979_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_4980_ = lean_nat_sub(v_fuel_4972_, v_one_4979_);
        v___x_4981_ = crate::leanh::lean_apply_1(v_h__2_4974_, v_n_4980_);
        return v___x_4981_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(
    mut v_motive_4982_: *mut crate::leanh::LeanObject,
    mut v_fuel_4983_: *mut crate::leanh::LeanObject,
    mut v_h__1_4984_: *mut crate::leanh::LeanObject,
    mut v_h__2_4985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4986_ =
        l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(
            v_motive_4982_,
            v_fuel_4983_,
            v_h__1_4984_,
            v_h__2_4985_,
        );
    crate::leanh::lean_dec(v_fuel_4983_);
    return v_res_4986_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(
    mut v_m_u2081_4987_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4988_: *mut crate::leanh::LeanObject,
    mut v_h__1_4989_: *mut crate::leanh::LeanObject,
    mut v_h__2_4990_: *mut crate::leanh::LeanObject,
    mut v_h__3_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2082_4988_) == 0 {
        let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4991_);
        crate::leanh::lean_dec(v_h__2_4990_);
        v___x_4992_ = crate::leanh::lean_apply_1(v_h__1_4989_, v_m_u2081_4987_);
        return v___x_4992_;
    } else {
        crate::leanh::lean_dec(v_h__1_4989_);
        if crate::leanh::lean_obj_tag(v_m_u2081_4987_) == 0 {
            let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4991_);
            v___x_4993_ = crate::leanh::lean_apply_2(
                v_h__2_4990_,
                v_m_u2082_4988_,
                crate::leanh::lean_box(0),
            );
            return v___x_4993_;
        } else {
            let mut v_p_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4990_);
            v_p_4994_ = crate::leanh::lean_ctor_get(v_m_u2082_4988_, 0);
            crate::leanh::lean_inc_ref(v_p_4994_);
            v_m_4995_ = crate::leanh::lean_ctor_get(v_m_u2082_4988_, 1);
            crate::leanh::lean_inc(v_m_4995_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_4988_, 2);
            v_p_4996_ = crate::leanh::lean_ctor_get(v_m_u2081_4987_, 0);
            crate::leanh::lean_inc_ref(v_p_4996_);
            v_m_4997_ = crate::leanh::lean_ctor_get(v_m_u2081_4987_, 1);
            crate::leanh::lean_inc(v_m_4997_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_4987_, 2);
            v___x_4998_ = crate::leanh::lean_apply_4(
                v_h__3_4991_,
                v_p_4996_,
                v_m_4997_,
                v_p_4994_,
                v_m_4995_,
            );
            return v___x_4998_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(
    mut v_motive_4999_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5000_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5001_: *mut crate::leanh::LeanObject,
    mut v_h__1_5002_: *mut crate::leanh::LeanObject,
    mut v_h__2_5003_: *mut crate::leanh::LeanObject,
    mut v_h__3_5004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2082_5001_) == 0 {
        let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5004_);
        crate::leanh::lean_dec(v_h__2_5003_);
        v___x_5005_ = crate::leanh::lean_apply_1(v_h__1_5002_, v_m_u2081_5000_);
        return v___x_5005_;
    } else {
        crate::leanh::lean_dec(v_h__1_5002_);
        if crate::leanh::lean_obj_tag(v_m_u2081_5000_) == 0 {
            let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5004_);
            v___x_5006_ = crate::leanh::lean_apply_2(
                v_h__2_5003_,
                v_m_u2082_5001_,
                crate::leanh::lean_box(0),
            );
            return v___x_5006_;
        } else {
            let mut v_p_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5003_);
            v_p_5007_ = crate::leanh::lean_ctor_get(v_m_u2082_5001_, 0);
            crate::leanh::lean_inc_ref(v_p_5007_);
            v_m_5008_ = crate::leanh::lean_ctor_get(v_m_u2082_5001_, 1);
            crate::leanh::lean_inc(v_m_5008_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_5001_, 2);
            v_p_5009_ = crate::leanh::lean_ctor_get(v_m_u2081_5000_, 0);
            crate::leanh::lean_inc_ref(v_p_5009_);
            v_m_5010_ = crate::leanh::lean_ctor_get(v_m_u2081_5000_, 1);
            crate::leanh::lean_inc(v_m_5010_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_5000_, 2);
            v___x_5011_ = crate::leanh::lean_apply_4(
                v_h__3_5004_,
                v_p_5009_,
                v_m_5010_,
                v_p_5007_,
                v_m_5008_,
            );
            return v___x_5011_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul__nc(
    mut v_m_u2081_5012_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_m_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut v_unused_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_u2081_5012_) == 0 {
                    return v_m_u2082_5013_;
                } else {
                    v_m_5014_ = crate::leanh::lean_ctor_get(v_m_u2081_5012_, 1);
                    if crate::leanh::lean_obj_tag(v_m_5014_) == 0 {
                        v_p_5015_ = crate::leanh::lean_ctor_get(v_m_u2081_5012_, 0);
                        crate::leanh::lean_inc_ref(v_p_5015_);
                        crate::leanh::lean_dec_ref_known(v_m_u2081_5012_, 2);
                        v___x_5016_ =
                            l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_5015_, v_m_u2082_5013_);
                        return v___x_5016_;
                    } else {
                        crate::leanh::lean_inc(v_m_5014_);
                        v_p_5017_ = crate::leanh::lean_ctor_get(v_m_u2081_5012_, 0);
                        v_isSharedCheck_5025_ =
                            (!crate::leanh::lean_is_exclusive(v_m_u2081_5012_)) as u8;
                        if v_isSharedCheck_5025_ == 0 {
                            v_unused_5026_ = crate::leanh::lean_ctor_get(v_m_u2081_5012_, 1);
                            crate::leanh::lean_dec(v_unused_5026_);
                            v___x_5019_ = v_m_u2081_5012_;
                            v_isShared_5020_ = v_isSharedCheck_5025_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_p_5017_);
                            crate::leanh::lean_dec(v_m_u2081_5012_);
                            v___x_5019_ = crate::leanh::lean_box(0);
                            v_isShared_5020_ = v_isSharedCheck_5025_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5021_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_5014_, v_m_u2082_5013_);
                if v_isShared_5020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5019_, 1, v___x_5021_);
                    v___x_5023_ = v___x_5019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_p_5017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5021_);
                    v___x_5023_ = v_reuseFailAlloc_5024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degree(
    mut v_x_5027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5027_) == 0 {
        let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5028_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5028_;
    } else {
        let mut v_p_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_5029_ = crate::leanh::lean_ctor_get(v_x_5027_, 0);
        v_m_5030_ = crate::leanh::lean_ctor_get(v_x_5027_, 1);
        v_k_5031_ = crate::leanh::lean_ctor_get(v_p_5029_, 1);
        v___x_5032_ = l_Lean_Grind_CommRing_Mon_degree(v_m_5030_);
        v___x_5033_ = lean_nat_add(v_k_5031_, v___x_5032_);
        crate::leanh::lean_dec(v___x_5032_);
        return v___x_5033_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degree___boxed(
    mut v_x_5034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5035_ = l_Lean_Grind_CommRing_Mon_degree(v_x_5034_);
    crate::leanh::lean_dec(v_x_5034_);
    return v_res_5035_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(
    mut v_x_5036_: *mut crate::leanh::LeanObject,
    mut v_h__1_5037_: *mut crate::leanh::LeanObject,
    mut v_h__2_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5036_) == 0 {
        let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5038_);
        v___x_5039_ = crate::leanh::lean_box(0);
        v___x_5040_ = crate::leanh::lean_apply_1(v_h__1_5037_, v___x_5039_);
        return v___x_5040_;
    } else {
        let mut v_p_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5037_);
        v_p_5041_ = crate::leanh::lean_ctor_get(v_x_5036_, 0);
        crate::leanh::lean_inc_ref(v_p_5041_);
        v_m_5042_ = crate::leanh::lean_ctor_get(v_x_5036_, 1);
        crate::leanh::lean_inc(v_m_5042_);
        crate::leanh::lean_dec_ref_known(v_x_5036_, 2);
        v___x_5043_ = crate::leanh::lean_apply_2(v_h__2_5038_, v_p_5041_, v_m_5042_);
        return v___x_5043_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(
    mut v_motive_5044_: *mut crate::leanh::LeanObject,
    mut v_x_5045_: *mut crate::leanh::LeanObject,
    mut v_h__1_5046_: *mut crate::leanh::LeanObject,
    mut v_h__2_5047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5045_) == 0 {
        let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5047_);
        v___x_5048_ = crate::leanh::lean_box(0);
        v___x_5049_ = crate::leanh::lean_apply_1(v_h__1_5046_, v___x_5048_);
        return v___x_5049_;
    } else {
        let mut v_p_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5046_);
        v_p_5050_ = crate::leanh::lean_ctor_get(v_x_5045_, 0);
        crate::leanh::lean_inc_ref(v_p_5050_);
        v_m_5051_ = crate::leanh::lean_ctor_get(v_x_5045_, 1);
        crate::leanh::lean_inc(v_m_5051_);
        crate::leanh::lean_dec_ref_known(v_x_5045_, 2);
        v___x_5052_ = crate::leanh::lean_apply_2(v_h__2_5047_, v_p_5050_, v_m_5051_);
        return v___x_5052_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Var_revlex(
    mut v_x_5053_: *mut crate::leanh::LeanObject,
    mut v_y_5054_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5055_: u8 = 0;
    v___x_5055_ = l_Nat_blt(v_x_5053_, v_y_5054_);
    if v___x_5055_ == 0 {
        let mut v___x_5056_: u8 = 0;
        v___x_5056_ = l_Nat_blt(v_y_5054_, v_x_5053_);
        if v___x_5056_ == 0 {
            let mut v___x_5057_: u8 = 0;
            v___x_5057_ = 1;
            return v___x_5057_;
        } else {
            let mut v___x_5058_: u8 = 0;
            v___x_5058_ = 0;
            return v___x_5058_;
        }
    } else {
        let mut v___x_5059_: u8 = 0;
        v___x_5059_ = 2;
        return v___x_5059_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Var_revlex___boxed(
    mut v_x_5060_: *mut crate::leanh::LeanObject,
    mut v_y_5061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5062_: u8 = 0;
    let mut v_r_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5062_ = l_Lean_Grind_CommRing_Var_revlex(v_x_5060_, v_y_5061_);
    crate::leanh::lean_dec(v_y_5061_);
    crate::leanh::lean_dec(v_x_5060_);
    v_r_5063_ = crate::leanh::lean_box((v_res_5062_) as usize);
    return v_r_5063_;
}
pub unsafe fn l_Lean_Grind_CommRing_powerRevlex(
    mut v_k_u2081_5064_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_5065_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5066_: u8 = 0;
    v___x_5066_ = l_Nat_blt(v_k_u2081_5064_, v_k_u2082_5065_);
    if v___x_5066_ == 0 {
        let mut v___x_5067_: u8 = 0;
        v___x_5067_ = l_Nat_blt(v_k_u2082_5065_, v_k_u2081_5064_);
        if v___x_5067_ == 0 {
            let mut v___x_5068_: u8 = 0;
            v___x_5068_ = 1;
            return v___x_5068_;
        } else {
            let mut v___x_5069_: u8 = 0;
            v___x_5069_ = 0;
            return v___x_5069_;
        }
    } else {
        let mut v___x_5070_: u8 = 0;
        v___x_5070_ = 2;
        return v___x_5070_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_powerRevlex___boxed(
    mut v_k_u2081_5071_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5073_: u8 = 0;
    let mut v_r_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_5071_, v_k_u2082_5072_);
    crate::leanh::lean_dec(v_k_u2082_5072_);
    crate::leanh::lean_dec(v_k_u2081_5071_);
    v_r_5074_ = crate::leanh::lean_box((v_res_5073_) as usize);
    return v_r_5074_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(
    mut v_c_5075_: u8,
    mut v_h__1_5076_: *mut crate::leanh::LeanObject,
    mut v_h__2_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_c_5075_ == 0 {
        let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5076_);
        v___x_5078_ = crate::leanh::lean_box(0);
        v___x_5079_ = crate::leanh::lean_apply_1(v_h__2_5077_, v___x_5078_);
        return v___x_5079_;
    } else {
        let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5077_);
        v___x_5080_ = crate::leanh::lean_box(0);
        v___x_5081_ = crate::leanh::lean_apply_1(v_h__1_5076_, v___x_5080_);
        return v___x_5081_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(
    mut v_c_5082_: *mut crate::leanh::LeanObject,
    mut v_h__1_5083_: *mut crate::leanh::LeanObject,
    mut v_h__2_5084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_26__boxed_5085_: u8 = 0;
    let mut v_res_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_26__boxed_5085_ = (crate::leanh::lean_unbox(v_c_5082_) as u8);
    v_res_5086_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(
        v_c_26__boxed_5085_,
        v_h__1_5083_,
        v_h__2_5084_,
    );
    return v_res_5086_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(
    mut v_motive_5087_: *mut crate::leanh::LeanObject,
    mut v_c_5088_: u8,
    mut v_h__1_5089_: *mut crate::leanh::LeanObject,
    mut v_h__2_5090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_c_5088_ == 0 {
        let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5089_);
        v___x_5091_ = crate::leanh::lean_box(0);
        v___x_5092_ = crate::leanh::lean_apply_1(v_h__2_5090_, v___x_5091_);
        return v___x_5092_;
    } else {
        let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5090_);
        v___x_5093_ = crate::leanh::lean_box(0);
        v___x_5094_ = crate::leanh::lean_apply_1(v_h__1_5089_, v___x_5093_);
        return v___x_5094_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(
    mut v_motive_5095_: *mut crate::leanh::LeanObject,
    mut v_c_5096_: *mut crate::leanh::LeanObject,
    mut v_h__1_5097_: *mut crate::leanh::LeanObject,
    mut v_h__2_5098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_37__boxed_5099_: u8 = 0;
    let mut v_res_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_37__boxed_5099_ = (crate::leanh::lean_unbox(v_c_5096_) as u8);
    v_res_5100_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(
        v_motive_5095_,
        v_c_37__boxed_5099_,
        v_h__1_5097_,
        v_h__2_5098_,
    );
    return v_res_5100_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_revlex(
    mut v_p_u2081_5101_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_5102_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    v_x_5103_ = crate::leanh::lean_ctor_get(v_p_u2081_5101_, 0);
    v_k_5104_ = crate::leanh::lean_ctor_get(v_p_u2081_5101_, 1);
    v_x_5105_ = crate::leanh::lean_ctor_get(v_p_u2082_5102_, 0);
    v_k_5106_ = crate::leanh::lean_ctor_get(v_p_u2082_5102_, 1);
    v___x_5107_ = l_Lean_Grind_CommRing_Var_revlex(v_x_5103_, v_x_5105_);
    if v___x_5107_ == 1 {
        let mut v___x_5108_: u8 = 0;
        v___x_5108_ = l_Lean_Grind_CommRing_powerRevlex(v_k_5104_, v_k_5106_);
        return v___x_5108_;
    } else {
        return v___x_5107_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_revlex___boxed(
    mut v_p_u2081_5109_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5111_: u8 = 0;
    let mut v_r_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5111_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_5109_, v_p_u2082_5110_);
    crate::leanh::lean_dec_ref(v_p_u2082_5110_);
    crate::leanh::lean_dec_ref(v_p_u2081_5109_);
    v_r_5112_ = crate::leanh::lean_box((v_res_5111_) as usize);
    return v_r_5112_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlexWF(
    mut v_m_u2081_5113_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5114_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_m_u2081_5113_) == 0 {
        if crate::leanh::lean_obj_tag(v_m_u2082_5114_) == 0 {
            let mut v___x_5115_: u8 = 0;
            v___x_5115_ = 1;
            return v___x_5115_;
        } else {
            let mut v___x_5116_: u8 = 0;
            v___x_5116_ = 2;
            return v___x_5116_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_m_u2082_5114_) == 0 {
            let mut v___x_5117_: u8 = 0;
            v___x_5117_ = 0;
            return v___x_5117_;
        } else {
            let mut v_p_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5126_: u8 = 0;
            v_p_5118_ = crate::leanh::lean_ctor_get(v_m_u2081_5113_, 0);
            v_p_5119_ = crate::leanh::lean_ctor_get(v_m_u2082_5114_, 0);
            v_m_5120_ = crate::leanh::lean_ctor_get(v_m_u2081_5113_, 1);
            v_m_5121_ = crate::leanh::lean_ctor_get(v_m_u2082_5114_, 1);
            v_x_5122_ = crate::leanh::lean_ctor_get(v_p_5118_, 0);
            v_k_5123_ = crate::leanh::lean_ctor_get(v_p_5118_, 1);
            v_x_5124_ = crate::leanh::lean_ctor_get(v_p_5119_, 0);
            v_k_5125_ = crate::leanh::lean_ctor_get(v_p_5119_, 1);
            v___x_5126_ = lean_nat_dec_eq(v_x_5122_, v_x_5124_);
            if v___x_5126_ == 0 {
                let mut v___x_5127_: u8 = 0;
                v___x_5127_ = l_Nat_blt(v_x_5122_, v_x_5124_);
                if v___x_5127_ == 0 {
                    let mut v___x_5128_: u8 = 0;
                    v___x_5128_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_5113_, v_m_5121_);
                    if v___x_5128_ == 1 {
                        let mut v___x_5129_: u8 = 0;
                        v___x_5129_ = 2;
                        return v___x_5129_;
                    } else {
                        return v___x_5128_;
                    }
                } else {
                    let mut v___x_5130_: u8 = 0;
                    v___x_5130_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_5120_, v_m_u2082_5114_);
                    if v___x_5130_ == 1 {
                        let mut v___x_5131_: u8 = 0;
                        v___x_5131_ = 0;
                        return v___x_5131_;
                    } else {
                        return v___x_5130_;
                    }
                }
            } else {
                let mut v___x_5132_: u8 = 0;
                v___x_5132_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_5120_, v_m_5121_);
                if v___x_5132_ == 1 {
                    let mut v___x_5133_: u8 = 0;
                    v___x_5133_ = l_Lean_Grind_CommRing_powerRevlex(v_k_5123_, v_k_5125_);
                    return v___x_5133_;
                } else {
                    return v___x_5132_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlexWF___boxed(
    mut v_m_u2081_5134_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5136_: u8 = 0;
    let mut v_r_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_5134_, v_m_u2082_5135_);
    crate::leanh::lean_dec(v_m_u2082_5135_);
    crate::leanh::lean_dec(v_m_u2081_5134_);
    v_r_5137_ = crate::leanh::lean_box((v_res_5136_) as usize);
    return v_r_5137_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(
    mut v_m_u2081_5138_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5139_: *mut crate::leanh::LeanObject,
    mut v_h__1_5140_: *mut crate::leanh::LeanObject,
    mut v_h__2_5141_: *mut crate::leanh::LeanObject,
    mut v_h__3_5142_: *mut crate::leanh::LeanObject,
    mut v_h__4_5143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2081_5138_) == 0 {
        crate::leanh::lean_dec(v_h__4_5143_);
        crate::leanh::lean_dec(v_h__3_5142_);
        if crate::leanh::lean_obj_tag(v_m_u2082_5139_) == 0 {
            let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5141_);
            v___x_5144_ = crate::leanh::lean_box(0);
            v___x_5145_ = crate::leanh::lean_apply_1(v_h__1_5140_, v___x_5144_);
            return v___x_5145_;
        } else {
            let mut v_p_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_5140_);
            v_p_5146_ = crate::leanh::lean_ctor_get(v_m_u2082_5139_, 0);
            crate::leanh::lean_inc_ref(v_p_5146_);
            v_m_5147_ = crate::leanh::lean_ctor_get(v_m_u2082_5139_, 1);
            crate::leanh::lean_inc(v_m_5147_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_5139_, 2);
            v___x_5148_ = crate::leanh::lean_apply_2(v_h__2_5141_, v_p_5146_, v_m_5147_);
            return v___x_5148_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_5141_);
        crate::leanh::lean_dec(v_h__1_5140_);
        if crate::leanh::lean_obj_tag(v_m_u2082_5139_) == 0 {
            let mut v_p_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_5143_);
            v_p_5149_ = crate::leanh::lean_ctor_get(v_m_u2081_5138_, 0);
            crate::leanh::lean_inc_ref(v_p_5149_);
            v_m_5150_ = crate::leanh::lean_ctor_get(v_m_u2081_5138_, 1);
            crate::leanh::lean_inc(v_m_5150_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_5138_, 2);
            v___x_5151_ = crate::leanh::lean_apply_2(v_h__3_5142_, v_p_5149_, v_m_5150_);
            return v___x_5151_;
        } else {
            let mut v_p_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5142_);
            v_p_5152_ = crate::leanh::lean_ctor_get(v_m_u2081_5138_, 0);
            crate::leanh::lean_inc_ref(v_p_5152_);
            v_m_5153_ = crate::leanh::lean_ctor_get(v_m_u2081_5138_, 1);
            crate::leanh::lean_inc(v_m_5153_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_5138_, 2);
            v_p_5154_ = crate::leanh::lean_ctor_get(v_m_u2082_5139_, 0);
            crate::leanh::lean_inc_ref(v_p_5154_);
            v_m_5155_ = crate::leanh::lean_ctor_get(v_m_u2082_5139_, 1);
            crate::leanh::lean_inc(v_m_5155_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_5139_, 2);
            v___x_5156_ = crate::leanh::lean_apply_4(
                v_h__4_5143_,
                v_p_5152_,
                v_m_5153_,
                v_p_5154_,
                v_m_5155_,
            );
            return v___x_5156_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(
    mut v_motive_5157_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5158_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5159_: *mut crate::leanh::LeanObject,
    mut v_h__1_5160_: *mut crate::leanh::LeanObject,
    mut v_h__2_5161_: *mut crate::leanh::LeanObject,
    mut v_h__3_5162_: *mut crate::leanh::LeanObject,
    mut v_h__4_5163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2081_5158_) == 0 {
        crate::leanh::lean_dec(v_h__4_5163_);
        crate::leanh::lean_dec(v_h__3_5162_);
        if crate::leanh::lean_obj_tag(v_m_u2082_5159_) == 0 {
            let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5161_);
            v___x_5164_ = crate::leanh::lean_box(0);
            v___x_5165_ = crate::leanh::lean_apply_1(v_h__1_5160_, v___x_5164_);
            return v___x_5165_;
        } else {
            let mut v_p_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_5160_);
            v_p_5166_ = crate::leanh::lean_ctor_get(v_m_u2082_5159_, 0);
            crate::leanh::lean_inc_ref(v_p_5166_);
            v_m_5167_ = crate::leanh::lean_ctor_get(v_m_u2082_5159_, 1);
            crate::leanh::lean_inc(v_m_5167_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_5159_, 2);
            v___x_5168_ = crate::leanh::lean_apply_2(v_h__2_5161_, v_p_5166_, v_m_5167_);
            return v___x_5168_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_5161_);
        crate::leanh::lean_dec(v_h__1_5160_);
        if crate::leanh::lean_obj_tag(v_m_u2082_5159_) == 0 {
            let mut v_p_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_5163_);
            v_p_5169_ = crate::leanh::lean_ctor_get(v_m_u2081_5158_, 0);
            crate::leanh::lean_inc_ref(v_p_5169_);
            v_m_5170_ = crate::leanh::lean_ctor_get(v_m_u2081_5158_, 1);
            crate::leanh::lean_inc(v_m_5170_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_5158_, 2);
            v___x_5171_ = crate::leanh::lean_apply_2(v_h__3_5162_, v_p_5169_, v_m_5170_);
            return v___x_5171_;
        } else {
            let mut v_p_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5162_);
            v_p_5172_ = crate::leanh::lean_ctor_get(v_m_u2081_5158_, 0);
            crate::leanh::lean_inc_ref(v_p_5172_);
            v_m_5173_ = crate::leanh::lean_ctor_get(v_m_u2081_5158_, 1);
            crate::leanh::lean_inc(v_m_5173_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_5158_, 2);
            v_p_5174_ = crate::leanh::lean_ctor_get(v_m_u2082_5159_, 0);
            crate::leanh::lean_inc_ref(v_p_5174_);
            v_m_5175_ = crate::leanh::lean_ctor_get(v_m_u2082_5159_, 1);
            crate::leanh::lean_inc(v_m_5175_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_5159_, 2);
            v___x_5176_ = crate::leanh::lean_apply_4(
                v_h__4_5163_,
                v_p_5172_,
                v_m_5173_,
                v_p_5174_,
                v_m_5175_,
            );
            return v___x_5176_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlexFuel(
    mut v_fuel_5177_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5178_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5179_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5181_: u8 = 0;
    v_zero_5180_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_5181_ = lean_nat_dec_eq(v_fuel_5177_, v_zero_5180_);
    if v_isZero_5181_ == 1 {
        let mut v___x_5182_: u8 = 0;
        v___x_5182_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_5178_, v_m_u2082_5179_);
        return v___x_5182_;
    } else {
        if crate::leanh::lean_obj_tag(v_m_u2081_5178_) == 0 {
            if crate::leanh::lean_obj_tag(v_m_u2082_5179_) == 0 {
                let mut v___x_5183_: u8 = 0;
                v___x_5183_ = 1;
                return v___x_5183_;
            } else {
                let mut v___x_5184_: u8 = 0;
                v___x_5184_ = 2;
                return v___x_5184_;
            }
        } else {
            if crate::leanh::lean_obj_tag(v_m_u2082_5179_) == 0 {
                let mut v___x_5185_: u8 = 0;
                v___x_5185_ = 0;
                return v___x_5185_;
            } else {
                let mut v_p_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_p_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_m_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_m_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_n_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5196_: u8 = 0;
                v_p_5186_ = crate::leanh::lean_ctor_get(v_m_u2081_5178_, 0);
                v_p_5187_ = crate::leanh::lean_ctor_get(v_m_u2082_5179_, 0);
                v_m_5188_ = crate::leanh::lean_ctor_get(v_m_u2081_5178_, 1);
                v_m_5189_ = crate::leanh::lean_ctor_get(v_m_u2082_5179_, 1);
                v_x_5190_ = crate::leanh::lean_ctor_get(v_p_5186_, 0);
                v_k_5191_ = crate::leanh::lean_ctor_get(v_p_5186_, 1);
                v_x_5192_ = crate::leanh::lean_ctor_get(v_p_5187_, 0);
                v_k_5193_ = crate::leanh::lean_ctor_get(v_p_5187_, 1);
                v_one_5194_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_5195_ = lean_nat_sub(v_fuel_5177_, v_one_5194_);
                v___x_5196_ = lean_nat_dec_eq(v_x_5190_, v_x_5192_);
                if v___x_5196_ == 0 {
                    let mut v___x_5197_: u8 = 0;
                    v___x_5197_ = l_Nat_blt(v_x_5190_, v_x_5192_);
                    if v___x_5197_ == 0 {
                        let mut v___x_5198_: u8 = 0;
                        v___x_5198_ = l_Lean_Grind_CommRing_Mon_revlexFuel(
                            v_n_5195_,
                            v_m_u2081_5178_,
                            v_m_5189_,
                        );
                        crate::leanh::lean_dec(v_n_5195_);
                        if v___x_5198_ == 1 {
                            let mut v___x_5199_: u8 = 0;
                            v___x_5199_ = 2;
                            return v___x_5199_;
                        } else {
                            return v___x_5198_;
                        }
                    } else {
                        let mut v___x_5200_: u8 = 0;
                        v___x_5200_ = l_Lean_Grind_CommRing_Mon_revlexFuel(
                            v_n_5195_,
                            v_m_5188_,
                            v_m_u2082_5179_,
                        );
                        crate::leanh::lean_dec(v_n_5195_);
                        if v___x_5200_ == 1 {
                            let mut v___x_5201_: u8 = 0;
                            v___x_5201_ = 0;
                            return v___x_5201_;
                        } else {
                            return v___x_5200_;
                        }
                    }
                } else {
                    let mut v___x_5202_: u8 = 0;
                    v___x_5202_ =
                        l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_5195_, v_m_5188_, v_m_5189_);
                    crate::leanh::lean_dec(v_n_5195_);
                    if v___x_5202_ == 1 {
                        let mut v___x_5203_: u8 = 0;
                        v___x_5203_ = l_Lean_Grind_CommRing_powerRevlex(v_k_5191_, v_k_5193_);
                        return v___x_5203_;
                    } else {
                        return v___x_5202_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(
    mut v_fuel_5204_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5205_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5207_: u8 = 0;
    let mut v_r_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5207_ =
        l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_5204_, v_m_u2081_5205_, v_m_u2082_5206_);
    crate::leanh::lean_dec(v_m_u2082_5206_);
    crate::leanh::lean_dec(v_m_u2081_5205_);
    crate::leanh::lean_dec(v_fuel_5204_);
    v_r_5208_ = crate::leanh::lean_box((v_res_5207_) as usize);
    return v_r_5208_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlex(
    mut v_m_u2081_5209_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5210_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: u8 = 0;
    v___x_5211_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_5212_ =
        l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_5211_, v_m_u2081_5209_, v_m_u2082_5210_);
    return v___x_5212_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlex___boxed(
    mut v_m_u2081_5213_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5215_: u8 = 0;
    let mut v_r_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5215_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_5213_, v_m_u2082_5214_);
    crate::leanh::lean_dec(v_m_u2082_5214_);
    crate::leanh::lean_dec(v_m_u2081_5213_);
    v_r_5216_ = crate::leanh::lean_box((v_res_5215_) as usize);
    return v_r_5216_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_grevlex(
    mut v_m_u2081_5217_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5218_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: u8 = 0;
    v___x_5219_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_5217_);
    v___x_5220_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_5218_);
    v___x_5221_ = lean_nat_dec_lt(v___x_5219_, v___x_5220_);
    if v___x_5221_ == 0 {
        let mut v___x_5222_: u8 = 0;
        v___x_5222_ = lean_nat_dec_eq(v___x_5219_, v___x_5220_);
        crate::leanh::lean_dec(v___x_5220_);
        crate::leanh::lean_dec(v___x_5219_);
        if v___x_5222_ == 0 {
            let mut v___x_5223_: u8 = 0;
            v___x_5223_ = 2;
            return v___x_5223_;
        } else {
            let mut v___x_5224_: u8 = 0;
            v___x_5224_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_5217_, v_m_u2082_5218_);
            return v___x_5224_;
        }
    } else {
        let mut v___x_5225_: u8 = 0;
        crate::leanh::lean_dec(v___x_5220_);
        crate::leanh::lean_dec(v___x_5219_);
        v___x_5225_ = 0;
        return v___x_5225_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_grevlex___boxed(
    mut v_m_u2081_5226_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5228_: u8 = 0;
    let mut v_r_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_5226_, v_m_u2082_5227_);
    crate::leanh::lean_dec(v_m_u2082_5227_);
    crate::leanh::lean_dec(v_m_u2081_5226_);
    v_r_5229_ = crate::leanh::lean_box((v_res_5228_) as usize);
    return v_r_5229_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorIdx(
    mut v_x_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5230_) == 0 {
        let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5231_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5231_;
    } else {
        let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5232_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_5232_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(
    mut v_x_5233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5234_ = l_Lean_Grind_CommRing_Poly_ctorIdx(v_x_5233_);
    crate::leanh::lean_dec_ref(v_x_5233_);
    return v_res_5234_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorElim___redArg(
    mut v_t_5235_: *mut crate::leanh::LeanObject,
    mut v_k_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5235_) == 0 {
        let mut v_k_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_5237_ = crate::leanh::lean_ctor_get(v_t_5235_, 0);
        crate::leanh::lean_inc(v_k_5237_);
        crate::leanh::lean_dec_ref_known(v_t_5235_, 1);
        v___x_5238_ = crate::leanh::lean_apply_1(v_k_5236_, v_k_5237_);
        return v___x_5238_;
    } else {
        let mut v_k_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_5239_ = crate::leanh::lean_ctor_get(v_t_5235_, 0);
        crate::leanh::lean_inc(v_k_5239_);
        v_v_5240_ = crate::leanh::lean_ctor_get(v_t_5235_, 1);
        crate::leanh::lean_inc(v_v_5240_);
        v_p_5241_ = crate::leanh::lean_ctor_get(v_t_5235_, 2);
        crate::leanh::lean_inc_ref(v_p_5241_);
        crate::leanh::lean_dec_ref_known(v_t_5235_, 3);
        v___x_5242_ = crate::leanh::lean_apply_3(v_k_5236_, v_k_5239_, v_v_5240_, v_p_5241_);
        return v___x_5242_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorElim(
    mut v_motive_5243_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5244_: *mut crate::leanh::LeanObject,
    mut v_t_5245_: *mut crate::leanh::LeanObject,
    mut v_h_5246_: *mut crate::leanh::LeanObject,
    mut v_k_5247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5248_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5245_, v_k_5247_);
    return v___x_5248_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorElim___boxed(
    mut v_motive_5249_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5250_: *mut crate::leanh::LeanObject,
    mut v_t_5251_: *mut crate::leanh::LeanObject,
    mut v_h_5252_: *mut crate::leanh::LeanObject,
    mut v_k_5253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5254_ = l_Lean_Grind_CommRing_Poly_ctorElim(
        v_motive_5249_,
        v_ctorIdx_5250_,
        v_t_5251_,
        v_h_5252_,
        v_k_5253_,
    );
    crate::leanh::lean_dec(v_ctorIdx_5250_);
    return v_res_5254_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_num_elim___redArg(
    mut v_t_5255_: *mut crate::leanh::LeanObject,
    mut v_num_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5255_, v_num_5256_);
    return v___x_5257_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_num_elim(
    mut v_motive_5258_: *mut crate::leanh::LeanObject,
    mut v_t_5259_: *mut crate::leanh::LeanObject,
    mut v_h_5260_: *mut crate::leanh::LeanObject,
    mut v_num_5261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5262_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5259_, v_num_5261_);
    return v___x_5262_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_add_elim___redArg(
    mut v_t_5263_: *mut crate::leanh::LeanObject,
    mut v_add_5264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5265_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5263_, v_add_5264_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_add_elim(
    mut v_motive_5266_: *mut crate::leanh::LeanObject,
    mut v_t_5267_: *mut crate::leanh::LeanObject,
    mut v_h_5268_: *mut crate::leanh::LeanObject,
    mut v_add_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5267_, v_add_5269_);
    return v___x_5270_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqPoly_beq(
    mut v_x_5271_: *mut crate::leanh::LeanObject,
    mut v_x_5272_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: u8 = 0;
    let mut v___x_5276_: u8 = 0;
    let mut v_k_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5271_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_5272_) == 0 {
                        v_k_5273_ = crate::leanh::lean_ctor_get(v_x_5271_, 0);
                        v_k_5274_ = crate::leanh::lean_ctor_get(v_x_5272_, 0);
                        v___x_5275_ = lean_int_dec_eq(v_k_5273_, v_k_5274_);
                        return v___x_5275_;
                    } else {
                        v___x_5276_ = 0;
                        return v___x_5276_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_5272_) == 1 {
                        v_k_5277_ = crate::leanh::lean_ctor_get(v_x_5271_, 0);
                        v_v_5278_ = crate::leanh::lean_ctor_get(v_x_5271_, 1);
                        v_p_5279_ = crate::leanh::lean_ctor_get(v_x_5271_, 2);
                        v_k_5280_ = crate::leanh::lean_ctor_get(v_x_5272_, 0);
                        v_v_5281_ = crate::leanh::lean_ctor_get(v_x_5272_, 1);
                        v_p_5282_ = crate::leanh::lean_ctor_get(v_x_5272_, 2);
                        v___x_5283_ = lean_int_dec_eq(v_k_5277_, v_k_5280_);
                        if v___x_5283_ == 0 {
                            return v___x_5283_;
                        } else {
                            v___x_5284_ =
                                l_Lean_Grind_CommRing_instBEqMon_beq(v_v_5278_, v_v_5281_);
                            if v___x_5284_ == 0 {
                                return v___x_5284_;
                            } else {
                                v_x_5271_ = v_p_5279_;
                                v_x_5272_ = v_p_5282_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v___x_5286_ = 0;
                        return v___x_5286_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(
    mut v_x_5287_: *mut crate::leanh::LeanObject,
    mut v_x_5288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5289_: u8 = 0;
    let mut v_r_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5289_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_5287_, v_x_5288_);
    crate::leanh::lean_dec_ref(v_x_5288_);
    crate::leanh::lean_dec_ref(v_x_5287_);
    v_r_5290_ = crate::leanh::lean_box((v_res_5289_) as usize);
    return v_r_5290_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(
    mut v_x_5293_: *mut crate::leanh::LeanObject,
    mut v_x_5294_: *mut crate::leanh::LeanObject,
    mut v_h__1_5295_: *mut crate::leanh::LeanObject,
    mut v_h__2_5296_: *mut crate::leanh::LeanObject,
    mut v_h__3_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5293_) == 0 {
        crate::leanh::lean_dec(v_h__2_5296_);
        if crate::leanh::lean_obj_tag(v_x_5294_) == 0 {
            let mut v_k_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5297_);
            v_k_5298_ = crate::leanh::lean_ctor_get(v_x_5293_, 0);
            crate::leanh::lean_inc(v_k_5298_);
            crate::leanh::lean_dec_ref_known(v_x_5293_, 1);
            v_k_5299_ = crate::leanh::lean_ctor_get(v_x_5294_, 0);
            crate::leanh::lean_inc(v_k_5299_);
            crate::leanh::lean_dec_ref_known(v_x_5294_, 1);
            v___x_5300_ = crate::leanh::lean_apply_2(v_h__1_5295_, v_k_5298_, v_k_5299_);
            return v___x_5300_;
        } else {
            let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_5295_);
            v___x_5301_ = crate::leanh::lean_apply_4(
                v_h__3_5297_,
                v_x_5293_,
                v_x_5294_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_5301_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_5295_);
        if crate::leanh::lean_obj_tag(v_x_5294_) == 1 {
            let mut v_k_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5297_);
            v_k_5302_ = crate::leanh::lean_ctor_get(v_x_5293_, 0);
            crate::leanh::lean_inc(v_k_5302_);
            v_v_5303_ = crate::leanh::lean_ctor_get(v_x_5293_, 1);
            crate::leanh::lean_inc(v_v_5303_);
            v_p_5304_ = crate::leanh::lean_ctor_get(v_x_5293_, 2);
            crate::leanh::lean_inc_ref(v_p_5304_);
            crate::leanh::lean_dec_ref_known(v_x_5293_, 3);
            v_k_5305_ = crate::leanh::lean_ctor_get(v_x_5294_, 0);
            crate::leanh::lean_inc(v_k_5305_);
            v_v_5306_ = crate::leanh::lean_ctor_get(v_x_5294_, 1);
            crate::leanh::lean_inc(v_v_5306_);
            v_p_5307_ = crate::leanh::lean_ctor_get(v_x_5294_, 2);
            crate::leanh::lean_inc_ref(v_p_5307_);
            crate::leanh::lean_dec_ref_known(v_x_5294_, 3);
            v___x_5308_ = crate::leanh::lean_apply_6(
                v_h__2_5296_,
                v_k_5302_,
                v_v_5303_,
                v_p_5304_,
                v_k_5305_,
                v_v_5306_,
                v_p_5307_,
            );
            return v___x_5308_;
        } else {
            let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5296_);
            v___x_5309_ = crate::leanh::lean_apply_4(
                v_h__3_5297_,
                v_x_5293_,
                v_x_5294_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_5309_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(
    mut v_motive_5310_: *mut crate::leanh::LeanObject,
    mut v_x_5311_: *mut crate::leanh::LeanObject,
    mut v_x_5312_: *mut crate::leanh::LeanObject,
    mut v_h__1_5313_: *mut crate::leanh::LeanObject,
    mut v_h__2_5314_: *mut crate::leanh::LeanObject,
    mut v_h__3_5315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5311_) == 0 {
        crate::leanh::lean_dec(v_h__2_5314_);
        if crate::leanh::lean_obj_tag(v_x_5312_) == 0 {
            let mut v_k_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5315_);
            v_k_5316_ = crate::leanh::lean_ctor_get(v_x_5311_, 0);
            crate::leanh::lean_inc(v_k_5316_);
            crate::leanh::lean_dec_ref_known(v_x_5311_, 1);
            v_k_5317_ = crate::leanh::lean_ctor_get(v_x_5312_, 0);
            crate::leanh::lean_inc(v_k_5317_);
            crate::leanh::lean_dec_ref_known(v_x_5312_, 1);
            v___x_5318_ = crate::leanh::lean_apply_2(v_h__1_5313_, v_k_5316_, v_k_5317_);
            return v___x_5318_;
        } else {
            let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_5313_);
            v___x_5319_ = crate::leanh::lean_apply_4(
                v_h__3_5315_,
                v_x_5311_,
                v_x_5312_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_5319_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_5313_);
        if crate::leanh::lean_obj_tag(v_x_5312_) == 1 {
            let mut v_k_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5315_);
            v_k_5320_ = crate::leanh::lean_ctor_get(v_x_5311_, 0);
            crate::leanh::lean_inc(v_k_5320_);
            v_v_5321_ = crate::leanh::lean_ctor_get(v_x_5311_, 1);
            crate::leanh::lean_inc(v_v_5321_);
            v_p_5322_ = crate::leanh::lean_ctor_get(v_x_5311_, 2);
            crate::leanh::lean_inc_ref(v_p_5322_);
            crate::leanh::lean_dec_ref_known(v_x_5311_, 3);
            v_k_5323_ = crate::leanh::lean_ctor_get(v_x_5312_, 0);
            crate::leanh::lean_inc(v_k_5323_);
            v_v_5324_ = crate::leanh::lean_ctor_get(v_x_5312_, 1);
            crate::leanh::lean_inc(v_v_5324_);
            v_p_5325_ = crate::leanh::lean_ctor_get(v_x_5312_, 2);
            crate::leanh::lean_inc_ref(v_p_5325_);
            crate::leanh::lean_dec_ref_known(v_x_5312_, 3);
            v___x_5326_ = crate::leanh::lean_apply_6(
                v_h__2_5314_,
                v_k_5320_,
                v_v_5321_,
                v_p_5322_,
                v_k_5323_,
                v_v_5324_,
                v_p_5325_,
            );
            return v___x_5326_;
        } else {
            let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5314_);
            v___x_5327_ = crate::leanh::lean_apply_4(
                v_h__3_5315_,
                v_x_5311_,
                v_x_5312_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_5327_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPoly_repr(
    mut v_x_5340_: *mut crate::leanh::LeanObject,
    mut v_prec_5341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: u8 = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___y_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: u8 = 0;
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_k_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: u8 = 0;
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: u8 = 0;
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5340_) == 0 {
                    v_k_5351_ = crate::leanh::lean_ctor_get(v_x_5340_, 0);
                    v_isSharedCheck_5374_ = (!crate::leanh::lean_is_exclusive(v_x_5340_)) as u8;
                    if v_isSharedCheck_5374_ == 0 {
                        v___x_5353_ = v_x_5340_;
                        v_isShared_5354_ = v_isSharedCheck_5374_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5351_);
                        crate::leanh::lean_dec(v_x_5340_);
                        v___x_5353_ = crate::leanh::lean_box(0);
                        v_isShared_5354_ = v_isSharedCheck_5374_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_5375_ = crate::leanh::lean_ctor_get(v_x_5340_, 0);
                    crate::leanh::lean_inc(v_k_5375_);
                    v_v_5376_ = crate::leanh::lean_ctor_get(v_x_5340_, 1);
                    crate::leanh::lean_inc(v_v_5376_);
                    v_p_5377_ = crate::leanh::lean_ctor_get(v_x_5340_, 2);
                    crate::leanh::lean_inc_ref(v_p_5377_);
                    crate::leanh::lean_dec_ref_known(v_x_5340_, 3);
                    v___x_5378_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_5406_ = lean_nat_dec_le(v___x_5378_, v_prec_5341_);
                    if v___x_5406_ == 0 {
                        v___x_5407_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                        );
                        v___y_5396_ = v___x_5407_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5408_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                            ),
                            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                        );
                        v___y_5396_ = v___x_5408_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5343_);
                v___x_5346_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5346_, 0, v___y_5343_);
                crate::leanh::lean_ctor_set(v___x_5346_, 1, v___y_5345_);
                crate::leanh::lean_inc(v___y_5344_);
                v___x_5347_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5347_, 0, v___y_5344_);
                crate::leanh::lean_ctor_set(v___x_5347_, 1, v___x_5346_);
                v___x_5348_ = 0;
                v___x_5349_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5349_, 0, v___x_5347_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5349_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5348_,
                );
                v___x_5350_ = l_Repr_addAppParen(v___x_5349_, v_prec_5341_);
                return v___x_5350_;
            }
            2 => {
                v___x_5370_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_5371_ = lean_nat_dec_le(v___x_5370_, v_prec_5341_);
                if v___x_5371_ == 0 {
                    v___x_5372_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3,
                    );
                    v___y_5356_ = v___x_5372_;
                    state = 3;
                    continue;
                } else {
                    v___x_5373_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___y_5356_ = v___x_5373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5357_ = l_Lean_Grind_CommRing_instReprPoly_repr___closed__2;
                v___x_5358_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_5359_ = lean_int_dec_lt(v_k_5351_, v___x_5358_);
                if v___x_5359_ == 0 {
                    v___x_5360_ = l_Int_repr(v_k_5351_);
                    crate::leanh::lean_dec(v_k_5351_);
                    if v_isShared_5354_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5353_, 3);
                        crate::leanh::lean_ctor_set(v___x_5353_, 0, v___x_5360_);
                        v___x_5362_ = v___x_5353_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5363_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5360_);
                        v___x_5362_ = v_reuseFailAlloc_5363_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_5364_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_5365_ = l_Int_repr(v_k_5351_);
                    crate::leanh::lean_dec(v_k_5351_);
                    if v_isShared_5354_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5353_, 3);
                        crate::leanh::lean_ctor_set(v___x_5353_, 0, v___x_5365_);
                        v___x_5367_ = v___x_5353_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5369_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5365_);
                        v___x_5367_ = v_reuseFailAlloc_5369_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___y_5343_ = v___x_5357_;
                v___y_5344_ = v___y_5356_;
                v___y_5345_ = v___x_5362_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5368_ = l_Repr_addAppParen(v___x_5367_, v___x_5364_);
                v___y_5343_ = v___x_5357_;
                v___y_5344_ = v___y_5356_;
                v___y_5345_ = v___x_5368_;
                state = 1;
                continue;
            }
            6 => {
                crate::leanh::lean_inc(v___y_5380_);
                v___x_5384_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5384_, 0, v___y_5380_);
                crate::leanh::lean_ctor_set(v___x_5384_, 1, v___y_5383_);
                crate::leanh::lean_inc_n(v___y_5382_, 2);
                v___x_5385_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5385_, 0, v___x_5384_);
                crate::leanh::lean_ctor_set(v___x_5385_, 1, v___y_5382_);
                v___x_5386_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_5376_, v___x_5378_);
                v___x_5387_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5387_, 0, v___x_5385_);
                crate::leanh::lean_ctor_set(v___x_5387_, 1, v___x_5386_);
                v___x_5388_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5388_, 0, v___x_5387_);
                crate::leanh::lean_ctor_set(v___x_5388_, 1, v___y_5382_);
                v___x_5389_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_5377_, v___x_5378_);
                v___x_5390_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5390_, 0, v___x_5388_);
                crate::leanh::lean_ctor_set(v___x_5390_, 1, v___x_5389_);
                crate::leanh::lean_inc(v___y_5381_);
                v___x_5391_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5391_, 0, v___y_5381_);
                crate::leanh::lean_ctor_set(v___x_5391_, 1, v___x_5390_);
                v___x_5392_ = 0;
                v___x_5393_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5393_, 0, v___x_5391_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5393_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5392_,
                );
                v___x_5394_ = l_Repr_addAppParen(v___x_5393_, v_prec_5341_);
                return v___x_5394_;
            }
            7 => {
                v___x_5397_ = crate::leanh::lean_box(1);
                v___x_5398_ = l_Lean_Grind_CommRing_instReprPoly_repr___closed__5;
                v___x_5399_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_5400_ = lean_int_dec_lt(v_k_5375_, v___x_5399_);
                if v___x_5400_ == 0 {
                    v___x_5401_ = l_Int_repr(v_k_5375_);
                    crate::leanh::lean_dec(v_k_5375_);
                    v___x_5402_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5402_, 0, v___x_5401_);
                    v___y_5380_ = v___x_5398_;
                    v___y_5381_ = v___y_5396_;
                    v___y_5382_ = v___x_5397_;
                    v___y_5383_ = v___x_5402_;
                    state = 6;
                    continue;
                } else {
                    v___x_5403_ = l_Int_repr(v_k_5375_);
                    crate::leanh::lean_dec(v_k_5375_);
                    v___x_5404_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5404_, 0, v___x_5403_);
                    v___x_5405_ = l_Repr_addAppParen(v___x_5404_, v___x_5378_);
                    v___y_5380_ = v___x_5398_;
                    v___y_5381_ = v___y_5396_;
                    v___y_5382_ = v___x_5397_;
                    v___y_5383_ = v___x_5405_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPoly_repr___boxed(
    mut v_x_5409_: *mut crate::leanh::LeanObject,
    mut v_prec_5410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5411_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_5409_, v_prec_5410_);
    crate::leanh::lean_dec(v_prec_5410_);
    return v_res_5411_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5414_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5415_, 0, v___x_5414_);
    return v___x_5415_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedPoly_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    return v___x_5416_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedPoly() -> *mut crate::leanh::LeanObject {
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5417_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
    return v___x_5417_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePoly_hash(
    mut v_x_5418_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_k_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: u64 = 0;
    let mut v_intZero_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_5422_: u8 = 0;
    let mut v_a_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: u64 = 0;
    let mut v___x_5427_: u64 = 0;
    let mut v_abs_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: u64 = 0;
    let mut v___x_5435_: u64 = 0;
    let mut v_k_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: u64 = 0;
    let mut v___y_5441_: u64 = 0;
    let mut v___x_5442_: u64 = 0;
    let mut v___x_5443_: u64 = 0;
    let mut v___x_5444_: u64 = 0;
    let mut v___x_5445_: u64 = 0;
    let mut v___x_5446_: u64 = 0;
    let mut v_intZero_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_5448_: u8 = 0;
    let mut v_a_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u64 = 0;
    let mut v_abs_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5418_) == 0 {
                    v_k_5419_ = crate::leanh::lean_ctor_get(v_x_5418_, 0);
                    v___x_5420_ = 0u64;
                    v_intZero_5421_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v_isNeg_5422_ = lean_int_dec_lt(v_k_5419_, v_intZero_5421_);
                    if v_isNeg_5422_ == 0 {
                        v_a_5423_ = lean_nat_abs(v_k_5419_);
                        v___x_5424_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5425_ = lean_nat_mul(v___x_5424_, v_a_5423_);
                        crate::leanh::lean_dec(v_a_5423_);
                        v___x_5426_ = lean_uint64_of_nat(v___x_5425_);
                        crate::leanh::lean_dec(v___x_5425_);
                        v___x_5427_ = lean_uint64_mix_hash(v___x_5420_, v___x_5426_);
                        return v___x_5427_;
                    } else {
                        v_abs_5428_ = lean_nat_abs(v_k_5419_);
                        v_one_5429_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_a_5430_ = lean_nat_sub(v_abs_5428_, v_one_5429_);
                        crate::leanh::lean_dec(v_abs_5428_);
                        v___x_5431_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5432_ = lean_nat_mul(v___x_5431_, v_a_5430_);
                        crate::leanh::lean_dec(v_a_5430_);
                        v___x_5433_ = lean_nat_add(v___x_5432_, v_one_5429_);
                        crate::leanh::lean_dec(v___x_5432_);
                        v___x_5434_ = lean_uint64_of_nat(v___x_5433_);
                        crate::leanh::lean_dec(v___x_5433_);
                        v___x_5435_ = lean_uint64_mix_hash(v___x_5420_, v___x_5434_);
                        return v___x_5435_;
                    }
                } else {
                    v_k_5436_ = crate::leanh::lean_ctor_get(v_x_5418_, 0);
                    v_v_5437_ = crate::leanh::lean_ctor_get(v_x_5418_, 1);
                    v_p_5438_ = crate::leanh::lean_ctor_get(v_x_5418_, 2);
                    v___x_5439_ = 1u64;
                    v_intZero_5447_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v_isNeg_5448_ = lean_int_dec_lt(v_k_5436_, v_intZero_5447_);
                    if v_isNeg_5448_ == 0 {
                        v_a_5449_ = lean_nat_abs(v_k_5436_);
                        v___x_5450_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5451_ = lean_nat_mul(v___x_5450_, v_a_5449_);
                        crate::leanh::lean_dec(v_a_5449_);
                        v___x_5452_ = lean_uint64_of_nat(v___x_5451_);
                        crate::leanh::lean_dec(v___x_5451_);
                        v___y_5441_ = v___x_5452_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_5453_ = lean_nat_abs(v_k_5436_);
                        v_one_5454_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_a_5455_ = lean_nat_sub(v_abs_5453_, v_one_5454_);
                        crate::leanh::lean_dec(v_abs_5453_);
                        v___x_5456_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5457_ = lean_nat_mul(v___x_5456_, v_a_5455_);
                        crate::leanh::lean_dec(v_a_5455_);
                        v___x_5458_ = lean_nat_add(v___x_5457_, v_one_5454_);
                        crate::leanh::lean_dec(v___x_5457_);
                        v___x_5459_ = lean_uint64_of_nat(v___x_5458_);
                        crate::leanh::lean_dec(v___x_5458_);
                        v___y_5441_ = v___x_5459_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5442_ = lean_uint64_mix_hash(v___x_5439_, v___y_5441_);
                v___x_5443_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_5437_);
                v___x_5444_ = lean_uint64_mix_hash(v___x_5442_, v___x_5443_);
                v___x_5445_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_5438_);
                v___x_5446_ = lean_uint64_mix_hash(v___x_5444_, v___x_5445_);
                return v___x_5446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(
    mut v_x_5460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5461_: u64 = 0;
    let mut v_r_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5461_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_5460_);
    crate::leanh::lean_dec_ref(v_x_5460_);
    v_r_5462_ = crate::leanh::lean_box_uint64(v_res_5461_);
    return v_r_5462_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote___redArg(
    mut v_inst_5465_: *mut crate::leanh::LeanObject,
    mut v_ctx_5466_: *mut crate::leanh::LeanObject,
    mut v_p_5467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCast_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_5468_ = crate::leanh::lean_ctor_get(v_inst_5465_, 0);
    v_intCast_5469_ = crate::leanh::lean_ctor_get(v_inst_5465_, 3);
    v_toAdd_5470_ = crate::leanh::lean_ctor_get(v_toSemiring_5468_, 0);
    crate::leanh::lean_inc(v_toAdd_5470_);
    crate::leanh::lean_inc_ref(v_inst_5465_);
    v___x_5471_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5465_);
    if crate::leanh::lean_obj_tag(v_p_5467_) == 0 {
        let mut v_k_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_intCast_5469_);
        crate::leanh::lean_dec_ref(v___x_5471_);
        crate::leanh::lean_dec(v_toAdd_5470_);
        crate::leanh::lean_dec_ref(v_inst_5465_);
        v_k_5472_ = crate::leanh::lean_ctor_get(v_p_5467_, 0);
        crate::leanh::lean_inc(v_k_5472_);
        crate::leanh::lean_dec_ref_known(v_p_5467_, 1);
        v___x_5473_ = crate::leanh::lean_apply_1(v_intCast_5469_, v_k_5472_);
        return v___x_5473_;
    } else {
        let mut v_zsmul_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_zsmul_5474_ = crate::leanh::lean_ctor_get(v___x_5471_, 2);
        crate::leanh::lean_inc(v_zsmul_5474_);
        crate::leanh::lean_dec_ref(v___x_5471_);
        v_k_5475_ = crate::leanh::lean_ctor_get(v_p_5467_, 0);
        crate::leanh::lean_inc(v_k_5475_);
        v_v_5476_ = crate::leanh::lean_ctor_get(v_p_5467_, 1);
        crate::leanh::lean_inc(v_v_5476_);
        v_p_5477_ = crate::leanh::lean_ctor_get(v_p_5467_, 2);
        crate::leanh::lean_inc_ref(v_p_5477_);
        crate::leanh::lean_dec_ref_known(v_p_5467_, 3);
        crate::leanh::lean_inc_ref(v_toSemiring_5468_);
        v___x_5478_ =
            l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_5468_, v_ctx_5466_, v_v_5476_);
        v___x_5479_ = crate::leanh::lean_apply_2(v_zsmul_5474_, v_k_5475_, v___x_5478_);
        v___x_5480_ =
            l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_5465_, v_ctx_5466_, v_p_5477_);
        v___x_5481_ = crate::leanh::lean_apply_2(v_toAdd_5470_, v___x_5479_, v___x_5480_);
        return v___x_5481_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(
    mut v_inst_5482_: *mut crate::leanh::LeanObject,
    mut v_ctx_5483_: *mut crate::leanh::LeanObject,
    mut v_p_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_5482_, v_ctx_5483_, v_p_5484_);
    crate::leanh::lean_dec_ref(v_ctx_5483_);
    return v_res_5485_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote(
    mut v_00_u03b1_5486_: *mut crate::leanh::LeanObject,
    mut v_inst_5487_: *mut crate::leanh::LeanObject,
    mut v_ctx_5488_: *mut crate::leanh::LeanObject,
    mut v_p_5489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_5487_, v_ctx_5488_, v_p_5489_);
    return v___x_5490_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote___boxed(
    mut v_00_u03b1_5491_: *mut crate::leanh::LeanObject,
    mut v_inst_5492_: *mut crate::leanh::LeanObject,
    mut v_ctx_5493_: *mut crate::leanh::LeanObject,
    mut v_p_5494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5495_ =
        l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_5491_, v_inst_5492_, v_ctx_5493_, v_p_5494_);
    crate::leanh::lean_dec_ref(v_ctx_5493_);
    return v_res_5495_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteTerm___redArg(
    mut v_inst_5496_: *mut crate::leanh::LeanObject,
    mut v_ctx_5497_: *mut crate::leanh::LeanObject,
    mut v_k_5498_: *mut crate::leanh::LeanObject,
    mut v_m_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmul_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: u8 = 0;
    v_toSemiring_5500_ = crate::leanh::lean_ctor_get(v_inst_5496_, 0);
    crate::leanh::lean_inc_ref(v_toSemiring_5500_);
    v___x_5501_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5496_);
    v_zsmul_5502_ = crate::leanh::lean_ctor_get(v___x_5501_, 2);
    crate::leanh::lean_inc(v_zsmul_5502_);
    crate::leanh::lean_dec_ref(v___x_5501_);
    v___x_5503_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5504_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_5505_ = lean_int_dec_eq(v_k_5498_, v___x_5504_);
    if v___x_5505_ == 0 {
        if crate::leanh::lean_obj_tag(v_m_5499_) == 0 {
            let mut v_ofNat_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_5506_ = crate::leanh::lean_ctor_get(v_toSemiring_5500_, 3);
            crate::leanh::lean_inc(v_ofNat_5506_);
            crate::leanh::lean_dec_ref(v_toSemiring_5500_);
            v___x_5507_ = crate::leanh::lean_apply_1(v_ofNat_5506_, v___x_5503_);
            v___x_5508_ = crate::leanh::lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5507_);
            return v___x_5508_;
        } else {
            let mut v_p_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_npow_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5516_: u8 = 0;
            v_p_5509_ = crate::leanh::lean_ctor_get(v_m_5499_, 0);
            crate::leanh::lean_inc_ref(v_p_5509_);
            v_m_5510_ = crate::leanh::lean_ctor_get(v_m_5499_, 1);
            crate::leanh::lean_inc(v_m_5510_);
            crate::leanh::lean_dec_ref_known(v_m_5499_, 2);
            v_ofNat_5511_ = crate::leanh::lean_ctor_get(v_toSemiring_5500_, 3);
            v_npow_5512_ = crate::leanh::lean_ctor_get(v_toSemiring_5500_, 5);
            v_x_5513_ = crate::leanh::lean_ctor_get(v_p_5509_, 0);
            crate::leanh::lean_inc(v_x_5513_);
            v_k_5514_ = crate::leanh::lean_ctor_get(v_p_5509_, 1);
            crate::leanh::lean_inc(v_k_5514_);
            crate::leanh::lean_dec_ref(v_p_5509_);
            v___x_5515_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_5516_ = lean_nat_dec_eq(v_k_5514_, v___x_5515_);
            if v___x_5516_ == 0 {
                let mut v___x_5517_: u8 = 0;
                v___x_5517_ = lean_nat_dec_eq(v_k_5514_, v___x_5503_);
                if v___x_5517_ == 0 {
                    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5518_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5513_);
                    crate::leanh::lean_dec(v_x_5513_);
                    crate::leanh::lean_inc(v_npow_5512_);
                    v___x_5519_ = crate::leanh::lean_apply_2(v_npow_5512_, v___x_5518_, v_k_5514_);
                    v___x_5520_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5510_,
                        v___x_5519_,
                    );
                    v___x_5521_ = crate::leanh::lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5520_);
                    return v___x_5521_;
                } else {
                    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5514_);
                    v___x_5522_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5513_);
                    crate::leanh::lean_dec(v_x_5513_);
                    v___x_5523_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5510_,
                        v___x_5522_,
                    );
                    v___x_5524_ = crate::leanh::lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5523_);
                    return v___x_5524_;
                }
            } else {
                let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_5514_);
                crate::leanh::lean_dec(v_x_5513_);
                crate::leanh::lean_inc(v_ofNat_5511_);
                v___x_5525_ = crate::leanh::lean_apply_1(v_ofNat_5511_, v___x_5503_);
                v___x_5526_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_toSemiring_5500_,
                    v_ctx_5497_,
                    v_m_5510_,
                    v___x_5525_,
                );
                v___x_5527_ = crate::leanh::lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5526_);
                return v___x_5527_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_zsmul_5502_);
        crate::leanh::lean_dec(v_k_5498_);
        if crate::leanh::lean_obj_tag(v_m_5499_) == 0 {
            let mut v_ofNat_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_5528_ = crate::leanh::lean_ctor_get(v_toSemiring_5500_, 3);
            crate::leanh::lean_inc(v_ofNat_5528_);
            crate::leanh::lean_dec_ref(v_toSemiring_5500_);
            v___x_5529_ = crate::leanh::lean_apply_1(v_ofNat_5528_, v___x_5503_);
            return v___x_5529_;
        } else {
            let mut v_p_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_npow_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5537_: u8 = 0;
            v_p_5530_ = crate::leanh::lean_ctor_get(v_m_5499_, 0);
            crate::leanh::lean_inc_ref(v_p_5530_);
            v_m_5531_ = crate::leanh::lean_ctor_get(v_m_5499_, 1);
            crate::leanh::lean_inc(v_m_5531_);
            crate::leanh::lean_dec_ref_known(v_m_5499_, 2);
            v_ofNat_5532_ = crate::leanh::lean_ctor_get(v_toSemiring_5500_, 3);
            v_npow_5533_ = crate::leanh::lean_ctor_get(v_toSemiring_5500_, 5);
            v_x_5534_ = crate::leanh::lean_ctor_get(v_p_5530_, 0);
            crate::leanh::lean_inc(v_x_5534_);
            v_k_5535_ = crate::leanh::lean_ctor_get(v_p_5530_, 1);
            crate::leanh::lean_inc(v_k_5535_);
            crate::leanh::lean_dec_ref(v_p_5530_);
            v___x_5536_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_5537_ = lean_nat_dec_eq(v_k_5535_, v___x_5536_);
            if v___x_5537_ == 0 {
                let mut v___x_5538_: u8 = 0;
                v___x_5538_ = lean_nat_dec_eq(v_k_5535_, v___x_5503_);
                if v___x_5538_ == 0 {
                    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5539_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5534_);
                    crate::leanh::lean_dec(v_x_5534_);
                    crate::leanh::lean_inc(v_npow_5533_);
                    v___x_5540_ = crate::leanh::lean_apply_2(v_npow_5533_, v___x_5539_, v_k_5535_);
                    v___x_5541_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5531_,
                        v___x_5540_,
                    );
                    return v___x_5541_;
                } else {
                    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5535_);
                    v___x_5542_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5534_);
                    crate::leanh::lean_dec(v_x_5534_);
                    v___x_5543_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5531_,
                        v___x_5542_,
                    );
                    return v___x_5543_;
                }
            } else {
                let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_5535_);
                crate::leanh::lean_dec(v_x_5534_);
                crate::leanh::lean_inc(v_ofNat_5532_);
                v___x_5544_ = crate::leanh::lean_apply_1(v_ofNat_5532_, v___x_5503_);
                v___x_5545_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_toSemiring_5500_,
                    v_ctx_5497_,
                    v_m_5531_,
                    v___x_5544_,
                );
                return v___x_5545_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(
    mut v_inst_5546_: *mut crate::leanh::LeanObject,
    mut v_ctx_5547_: *mut crate::leanh::LeanObject,
    mut v_k_5548_: *mut crate::leanh::LeanObject,
    mut v_m_5549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5550_ =
        l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_5546_, v_ctx_5547_, v_k_5548_, v_m_5549_);
    crate::leanh::lean_dec_ref(v_ctx_5547_);
    return v_res_5550_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteTerm(
    mut v_00_u03b1_5551_: *mut crate::leanh::LeanObject,
    mut v_inst_5552_: *mut crate::leanh::LeanObject,
    mut v_ctx_5553_: *mut crate::leanh::LeanObject,
    mut v_k_5554_: *mut crate::leanh::LeanObject,
    mut v_m_5555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmul_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: u8 = 0;
    v_toSemiring_5556_ = crate::leanh::lean_ctor_get(v_inst_5552_, 0);
    crate::leanh::lean_inc_ref(v_toSemiring_5556_);
    v___x_5557_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5552_);
    v_zsmul_5558_ = crate::leanh::lean_ctor_get(v___x_5557_, 2);
    crate::leanh::lean_inc(v_zsmul_5558_);
    crate::leanh::lean_dec_ref(v___x_5557_);
    v___x_5559_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5560_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_5561_ = lean_int_dec_eq(v_k_5554_, v___x_5560_);
    if v___x_5561_ == 0 {
        if crate::leanh::lean_obj_tag(v_m_5555_) == 0 {
            let mut v_ofNat_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_5562_ = crate::leanh::lean_ctor_get(v_toSemiring_5556_, 3);
            crate::leanh::lean_inc(v_ofNat_5562_);
            crate::leanh::lean_dec_ref(v_toSemiring_5556_);
            v___x_5563_ = crate::leanh::lean_apply_1(v_ofNat_5562_, v___x_5559_);
            v___x_5564_ = crate::leanh::lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5563_);
            return v___x_5564_;
        } else {
            let mut v_p_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_npow_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5572_: u8 = 0;
            v_p_5565_ = crate::leanh::lean_ctor_get(v_m_5555_, 0);
            crate::leanh::lean_inc_ref(v_p_5565_);
            v_m_5566_ = crate::leanh::lean_ctor_get(v_m_5555_, 1);
            crate::leanh::lean_inc(v_m_5566_);
            crate::leanh::lean_dec_ref_known(v_m_5555_, 2);
            v_ofNat_5567_ = crate::leanh::lean_ctor_get(v_toSemiring_5556_, 3);
            v_npow_5568_ = crate::leanh::lean_ctor_get(v_toSemiring_5556_, 5);
            v_x_5569_ = crate::leanh::lean_ctor_get(v_p_5565_, 0);
            crate::leanh::lean_inc(v_x_5569_);
            v_k_5570_ = crate::leanh::lean_ctor_get(v_p_5565_, 1);
            crate::leanh::lean_inc(v_k_5570_);
            crate::leanh::lean_dec_ref(v_p_5565_);
            v___x_5571_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_5572_ = lean_nat_dec_eq(v_k_5570_, v___x_5571_);
            if v___x_5572_ == 0 {
                let mut v___x_5573_: u8 = 0;
                v___x_5573_ = lean_nat_dec_eq(v_k_5570_, v___x_5559_);
                if v___x_5573_ == 0 {
                    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5574_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5569_);
                    crate::leanh::lean_dec(v_x_5569_);
                    crate::leanh::lean_inc(v_npow_5568_);
                    v___x_5575_ = crate::leanh::lean_apply_2(v_npow_5568_, v___x_5574_, v_k_5570_);
                    v___x_5576_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5566_,
                        v___x_5575_,
                    );
                    v___x_5577_ = crate::leanh::lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5576_);
                    return v___x_5577_;
                } else {
                    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5570_);
                    v___x_5578_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5569_);
                    crate::leanh::lean_dec(v_x_5569_);
                    v___x_5579_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5566_,
                        v___x_5578_,
                    );
                    v___x_5580_ = crate::leanh::lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5579_);
                    return v___x_5580_;
                }
            } else {
                let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_5570_);
                crate::leanh::lean_dec(v_x_5569_);
                crate::leanh::lean_inc(v_ofNat_5567_);
                v___x_5581_ = crate::leanh::lean_apply_1(v_ofNat_5567_, v___x_5559_);
                v___x_5582_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_toSemiring_5556_,
                    v_ctx_5553_,
                    v_m_5566_,
                    v___x_5581_,
                );
                v___x_5583_ = crate::leanh::lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5582_);
                return v___x_5583_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_zsmul_5558_);
        crate::leanh::lean_dec(v_k_5554_);
        if crate::leanh::lean_obj_tag(v_m_5555_) == 0 {
            let mut v_ofNat_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_5584_ = crate::leanh::lean_ctor_get(v_toSemiring_5556_, 3);
            crate::leanh::lean_inc(v_ofNat_5584_);
            crate::leanh::lean_dec_ref(v_toSemiring_5556_);
            v___x_5585_ = crate::leanh::lean_apply_1(v_ofNat_5584_, v___x_5559_);
            return v___x_5585_;
        } else {
            let mut v_p_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_npow_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5593_: u8 = 0;
            v_p_5586_ = crate::leanh::lean_ctor_get(v_m_5555_, 0);
            crate::leanh::lean_inc_ref(v_p_5586_);
            v_m_5587_ = crate::leanh::lean_ctor_get(v_m_5555_, 1);
            crate::leanh::lean_inc(v_m_5587_);
            crate::leanh::lean_dec_ref_known(v_m_5555_, 2);
            v_ofNat_5588_ = crate::leanh::lean_ctor_get(v_toSemiring_5556_, 3);
            v_npow_5589_ = crate::leanh::lean_ctor_get(v_toSemiring_5556_, 5);
            v_x_5590_ = crate::leanh::lean_ctor_get(v_p_5586_, 0);
            crate::leanh::lean_inc(v_x_5590_);
            v_k_5591_ = crate::leanh::lean_ctor_get(v_p_5586_, 1);
            crate::leanh::lean_inc(v_k_5591_);
            crate::leanh::lean_dec_ref(v_p_5586_);
            v___x_5592_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_5593_ = lean_nat_dec_eq(v_k_5591_, v___x_5592_);
            if v___x_5593_ == 0 {
                let mut v___x_5594_: u8 = 0;
                v___x_5594_ = lean_nat_dec_eq(v_k_5591_, v___x_5559_);
                if v___x_5594_ == 0 {
                    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5595_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5590_);
                    crate::leanh::lean_dec(v_x_5590_);
                    crate::leanh::lean_inc(v_npow_5589_);
                    v___x_5596_ = crate::leanh::lean_apply_2(v_npow_5589_, v___x_5595_, v_k_5591_);
                    v___x_5597_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5587_,
                        v___x_5596_,
                    );
                    return v___x_5597_;
                } else {
                    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5591_);
                    v___x_5598_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5590_);
                    crate::leanh::lean_dec(v_x_5590_);
                    v___x_5599_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5587_,
                        v___x_5598_,
                    );
                    return v___x_5599_;
                }
            } else {
                let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_5591_);
                crate::leanh::lean_dec(v_x_5590_);
                crate::leanh::lean_inc(v_ofNat_5588_);
                v___x_5600_ = crate::leanh::lean_apply_1(v_ofNat_5588_, v___x_5559_);
                v___x_5601_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_toSemiring_5556_,
                    v_ctx_5553_,
                    v_m_5587_,
                    v___x_5600_,
                );
                return v___x_5601_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteTerm___boxed(
    mut v_00_u03b1_5602_: *mut crate::leanh::LeanObject,
    mut v_inst_5603_: *mut crate::leanh::LeanObject,
    mut v_ctx_5604_: *mut crate::leanh::LeanObject,
    mut v_k_5605_: *mut crate::leanh::LeanObject,
    mut v_m_5606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5607_ = l_Lean_Grind_CommRing_denoteTerm(
        v_00_u03b1_5602_,
        v_inst_5603_,
        v_ctx_5604_,
        v_k_5605_,
        v_m_5606_,
    );
    crate::leanh::lean_dec_ref(v_ctx_5604_);
    return v_res_5607_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
    mut v_inst_5608_: *mut crate::leanh::LeanObject,
    mut v_ctx_5609_: *mut crate::leanh::LeanObject,
    mut v_p_5610_: *mut crate::leanh::LeanObject,
    mut v_acc_5611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCast_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmul_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: u8 = 0;
    let mut v___x_5644_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: u8 = 0;
    let mut v___x_5662_: u8 = 0;
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_5610_) == 0 {
                    v_toSemiring_5612_ = crate::leanh::lean_ctor_get(v_inst_5608_, 0);
                    crate::leanh::lean_inc_ref(v_toSemiring_5612_);
                    v_intCast_5613_ = crate::leanh::lean_ctor_get(v_inst_5608_, 3);
                    crate::leanh::lean_inc(v_intCast_5613_);
                    crate::leanh::lean_dec_ref(v_inst_5608_);
                    v_toAdd_5614_ = crate::leanh::lean_ctor_get(v_toSemiring_5612_, 0);
                    crate::leanh::lean_inc(v_toAdd_5614_);
                    crate::leanh::lean_dec_ref(v_toSemiring_5612_);
                    v_k_5615_ = crate::leanh::lean_ctor_get(v_p_5610_, 0);
                    crate::leanh::lean_inc(v_k_5615_);
                    crate::leanh::lean_dec_ref_known(v_p_5610_, 1);
                    v___x_5616_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v___x_5617_ = lean_int_dec_eq(v_k_5615_, v___x_5616_);
                    if v___x_5617_ == 0 {
                        v___x_5618_ = crate::leanh::lean_apply_1(v_intCast_5613_, v_k_5615_);
                        v___x_5619_ =
                            crate::leanh::lean_apply_2(v_toAdd_5614_, v_acc_5611_, v___x_5618_);
                        return v___x_5619_;
                    } else {
                        crate::leanh::lean_dec(v_k_5615_);
                        crate::leanh::lean_dec(v_toAdd_5614_);
                        crate::leanh::lean_dec(v_intCast_5613_);
                        return v_acc_5611_;
                    }
                } else {
                    v_toSemiring_5620_ = crate::leanh::lean_ctor_get(v_inst_5608_, 0);
                    v_toAdd_5621_ = crate::leanh::lean_ctor_get(v_toSemiring_5620_, 0);
                    v_ofNat_5622_ = crate::leanh::lean_ctor_get(v_toSemiring_5620_, 3);
                    v_npow_5623_ = crate::leanh::lean_ctor_get(v_toSemiring_5620_, 5);
                    v_k_5624_ = crate::leanh::lean_ctor_get(v_p_5610_, 0);
                    crate::leanh::lean_inc(v_k_5624_);
                    v_v_5625_ = crate::leanh::lean_ctor_get(v_p_5610_, 1);
                    crate::leanh::lean_inc(v_v_5625_);
                    v_p_5626_ = crate::leanh::lean_ctor_get(v_p_5610_, 2);
                    crate::leanh::lean_inc_ref(v_p_5626_);
                    crate::leanh::lean_dec_ref_known(v_p_5610_, 3);
                    crate::leanh::lean_inc_ref(v_inst_5608_);
                    v___x_5631_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5608_);
                    v_zsmul_5632_ = crate::leanh::lean_ctor_get(v___x_5631_, 2);
                    crate::leanh::lean_inc(v_zsmul_5632_);
                    crate::leanh::lean_dec_ref(v___x_5631_);
                    v___x_5633_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5634_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once
                        ),
                        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
                    );
                    v___x_5635_ = lean_int_dec_eq(v_k_5624_, v___x_5634_);
                    if v___x_5635_ == 0 {
                        if crate::leanh::lean_obj_tag(v_v_5625_) == 0 {
                            crate::leanh::lean_inc(v_ofNat_5622_);
                            v___x_5636_ = crate::leanh::lean_apply_1(v_ofNat_5622_, v___x_5633_);
                            v___x_5637_ =
                                crate::leanh::lean_apply_2(v_zsmul_5632_, v_k_5624_, v___x_5636_);
                            v___y_5628_ = v___x_5637_;
                            state = 1;
                            continue;
                        } else {
                            v_p_5638_ = crate::leanh::lean_ctor_get(v_v_5625_, 0);
                            crate::leanh::lean_inc_ref(v_p_5638_);
                            v_m_5639_ = crate::leanh::lean_ctor_get(v_v_5625_, 1);
                            crate::leanh::lean_inc(v_m_5639_);
                            crate::leanh::lean_dec_ref_known(v_v_5625_, 2);
                            v_x_5640_ = crate::leanh::lean_ctor_get(v_p_5638_, 0);
                            crate::leanh::lean_inc(v_x_5640_);
                            v_k_5641_ = crate::leanh::lean_ctor_get(v_p_5638_, 1);
                            crate::leanh::lean_inc(v_k_5641_);
                            crate::leanh::lean_dec_ref(v_p_5638_);
                            v___x_5642_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_5643_ = lean_nat_dec_eq(v_k_5641_, v___x_5642_);
                            if v___x_5643_ == 0 {
                                v___x_5644_ = lean_nat_dec_eq(v_k_5641_, v___x_5633_);
                                if v___x_5644_ == 0 {
                                    v___x_5645_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5640_);
                                    crate::leanh::lean_dec(v_x_5640_);
                                    crate::leanh::lean_inc(v_npow_5623_);
                                    v___x_5646_ = crate::leanh::lean_apply_2(
                                        v_npow_5623_,
                                        v___x_5645_,
                                        v_k_5641_,
                                    );
                                    crate::leanh::lean_inc_ref(v_toSemiring_5620_);
                                    v___x_5647_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                        v_toSemiring_5620_,
                                        v_ctx_5609_,
                                        v_m_5639_,
                                        v___x_5646_,
                                    );
                                    v___x_5648_ = crate::leanh::lean_apply_2(
                                        v_zsmul_5632_,
                                        v_k_5624_,
                                        v___x_5647_,
                                    );
                                    v___y_5628_ = v___x_5648_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_k_5641_);
                                    v___x_5649_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5640_);
                                    crate::leanh::lean_dec(v_x_5640_);
                                    crate::leanh::lean_inc_ref(v_toSemiring_5620_);
                                    v___x_5650_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                        v_toSemiring_5620_,
                                        v_ctx_5609_,
                                        v_m_5639_,
                                        v___x_5649_,
                                    );
                                    v___x_5651_ = crate::leanh::lean_apply_2(
                                        v_zsmul_5632_,
                                        v_k_5624_,
                                        v___x_5650_,
                                    );
                                    v___y_5628_ = v___x_5651_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_k_5641_);
                                crate::leanh::lean_dec(v_x_5640_);
                                crate::leanh::lean_inc(v_ofNat_5622_);
                                v___x_5652_ =
                                    crate::leanh::lean_apply_1(v_ofNat_5622_, v___x_5633_);
                                crate::leanh::lean_inc_ref(v_toSemiring_5620_);
                                v___x_5653_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                    v_toSemiring_5620_,
                                    v_ctx_5609_,
                                    v_m_5639_,
                                    v___x_5652_,
                                );
                                v___x_5654_ = crate::leanh::lean_apply_2(
                                    v_zsmul_5632_,
                                    v_k_5624_,
                                    v___x_5653_,
                                );
                                v___y_5628_ = v___x_5654_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_zsmul_5632_);
                        crate::leanh::lean_dec(v_k_5624_);
                        if crate::leanh::lean_obj_tag(v_v_5625_) == 0 {
                            crate::leanh::lean_inc(v_ofNat_5622_);
                            v___x_5655_ = crate::leanh::lean_apply_1(v_ofNat_5622_, v___x_5633_);
                            v___y_5628_ = v___x_5655_;
                            state = 1;
                            continue;
                        } else {
                            v_p_5656_ = crate::leanh::lean_ctor_get(v_v_5625_, 0);
                            crate::leanh::lean_inc_ref(v_p_5656_);
                            v_m_5657_ = crate::leanh::lean_ctor_get(v_v_5625_, 1);
                            crate::leanh::lean_inc(v_m_5657_);
                            crate::leanh::lean_dec_ref_known(v_v_5625_, 2);
                            v_x_5658_ = crate::leanh::lean_ctor_get(v_p_5656_, 0);
                            crate::leanh::lean_inc(v_x_5658_);
                            v_k_5659_ = crate::leanh::lean_ctor_get(v_p_5656_, 1);
                            crate::leanh::lean_inc(v_k_5659_);
                            crate::leanh::lean_dec_ref(v_p_5656_);
                            v___x_5660_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_5661_ = lean_nat_dec_eq(v_k_5659_, v___x_5660_);
                            if v___x_5661_ == 0 {
                                v___x_5662_ = lean_nat_dec_eq(v_k_5659_, v___x_5633_);
                                if v___x_5662_ == 0 {
                                    v___x_5663_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5658_);
                                    crate::leanh::lean_dec(v_x_5658_);
                                    crate::leanh::lean_inc(v_npow_5623_);
                                    v___x_5664_ = crate::leanh::lean_apply_2(
                                        v_npow_5623_,
                                        v___x_5663_,
                                        v_k_5659_,
                                    );
                                    crate::leanh::lean_inc_ref(v_toSemiring_5620_);
                                    v___x_5665_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                        v_toSemiring_5620_,
                                        v_ctx_5609_,
                                        v_m_5657_,
                                        v___x_5664_,
                                    );
                                    v___y_5628_ = v___x_5665_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_k_5659_);
                                    v___x_5666_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5658_);
                                    crate::leanh::lean_dec(v_x_5658_);
                                    crate::leanh::lean_inc_ref(v_toSemiring_5620_);
                                    v___x_5667_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                        v_toSemiring_5620_,
                                        v_ctx_5609_,
                                        v_m_5657_,
                                        v___x_5666_,
                                    );
                                    v___y_5628_ = v___x_5667_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_k_5659_);
                                crate::leanh::lean_dec(v_x_5658_);
                                crate::leanh::lean_inc(v_ofNat_5622_);
                                v___x_5668_ =
                                    crate::leanh::lean_apply_1(v_ofNat_5622_, v___x_5633_);
                                crate::leanh::lean_inc_ref(v_toSemiring_5620_);
                                v___x_5669_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                    v_toSemiring_5620_,
                                    v_ctx_5609_,
                                    v_m_5657_,
                                    v___x_5668_,
                                );
                                v___y_5628_ = v___x_5669_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toAdd_5621_);
                v___x_5629_ = crate::leanh::lean_apply_2(v_toAdd_5621_, v_acc_5611_, v___y_5628_);
                v_p_5610_ = v_p_5626_;
                v_acc_5611_ = v___x_5629_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(
    mut v_inst_5670_: *mut crate::leanh::LeanObject,
    mut v_ctx_5671_: *mut crate::leanh::LeanObject,
    mut v_p_5672_: *mut crate::leanh::LeanObject,
    mut v_acc_5673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5674_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
        v_inst_5670_,
        v_ctx_5671_,
        v_p_5672_,
        v_acc_5673_,
    );
    crate::leanh::lean_dec_ref(v_ctx_5671_);
    return v_res_5674_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go(
    mut v_00_u03b1_5675_: *mut crate::leanh::LeanObject,
    mut v_inst_5676_: *mut crate::leanh::LeanObject,
    mut v_ctx_5677_: *mut crate::leanh::LeanObject,
    mut v_p_5678_: *mut crate::leanh::LeanObject,
    mut v_acc_5679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5680_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
        v_inst_5676_,
        v_ctx_5677_,
        v_p_5678_,
        v_acc_5679_,
    );
    return v___x_5680_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(
    mut v_00_u03b1_5681_: *mut crate::leanh::LeanObject,
    mut v_inst_5682_: *mut crate::leanh::LeanObject,
    mut v_ctx_5683_: *mut crate::leanh::LeanObject,
    mut v_p_5684_: *mut crate::leanh::LeanObject,
    mut v_acc_5685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5686_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(
        v_00_u03b1_5681_,
        v_inst_5682_,
        v_ctx_5683_,
        v_p_5684_,
        v_acc_5685_,
    );
    crate::leanh::lean_dec_ref(v_ctx_5683_);
    return v_res_5686_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27___redArg(
    mut v_inst_5687_: *mut crate::leanh::LeanObject,
    mut v_ctx_5688_: *mut crate::leanh::LeanObject,
    mut v_p_5689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_5689_) == 0 {
        let mut v_intCast_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_intCast_5690_ = crate::leanh::lean_ctor_get(v_inst_5687_, 3);
        crate::leanh::lean_inc(v_intCast_5690_);
        crate::leanh::lean_dec_ref(v_inst_5687_);
        v_k_5691_ = crate::leanh::lean_ctor_get(v_p_5689_, 0);
        crate::leanh::lean_inc(v_k_5691_);
        crate::leanh::lean_dec_ref_known(v_p_5689_, 1);
        v___x_5692_ = crate::leanh::lean_apply_1(v_intCast_5690_, v_k_5691_);
        return v___x_5692_;
    } else {
        let mut v_toSemiring_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zsmul_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5701_: u8 = 0;
        v_toSemiring_5693_ = crate::leanh::lean_ctor_get(v_inst_5687_, 0);
        v_k_5694_ = crate::leanh::lean_ctor_get(v_p_5689_, 0);
        crate::leanh::lean_inc(v_k_5694_);
        v_v_5695_ = crate::leanh::lean_ctor_get(v_p_5689_, 1);
        crate::leanh::lean_inc(v_v_5695_);
        v_p_5696_ = crate::leanh::lean_ctor_get(v_p_5689_, 2);
        crate::leanh::lean_inc_ref(v_p_5696_);
        crate::leanh::lean_dec_ref_known(v_p_5689_, 3);
        crate::leanh::lean_inc_ref(v_inst_5687_);
        v___x_5697_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5687_);
        v_zsmul_5698_ = crate::leanh::lean_ctor_get(v___x_5697_, 2);
        crate::leanh::lean_inc(v_zsmul_5698_);
        crate::leanh::lean_dec_ref(v___x_5697_);
        v___x_5699_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5700_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_5701_ = lean_int_dec_eq(v_k_5694_, v___x_5700_);
        if v___x_5701_ == 0 {
            if crate::leanh::lean_obj_tag(v_v_5695_) == 0 {
                let mut v_ofNat_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ofNat_5702_ = crate::leanh::lean_ctor_get(v_toSemiring_5693_, 3);
                crate::leanh::lean_inc(v_ofNat_5702_);
                v___x_5703_ = crate::leanh::lean_apply_1(v_ofNat_5702_, v___x_5699_);
                v___x_5704_ = crate::leanh::lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5703_);
                v___x_5705_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5687_,
                    v_ctx_5688_,
                    v_p_5696_,
                    v___x_5704_,
                );
                return v___x_5705_;
            } else {
                let mut v_p_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_m_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_npow_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5713_: u8 = 0;
                v_p_5706_ = crate::leanh::lean_ctor_get(v_v_5695_, 0);
                crate::leanh::lean_inc_ref(v_p_5706_);
                v_m_5707_ = crate::leanh::lean_ctor_get(v_v_5695_, 1);
                crate::leanh::lean_inc(v_m_5707_);
                crate::leanh::lean_dec_ref_known(v_v_5695_, 2);
                v_ofNat_5708_ = crate::leanh::lean_ctor_get(v_toSemiring_5693_, 3);
                v_npow_5709_ = crate::leanh::lean_ctor_get(v_toSemiring_5693_, 5);
                v_x_5710_ = crate::leanh::lean_ctor_get(v_p_5706_, 0);
                crate::leanh::lean_inc(v_x_5710_);
                v_k_5711_ = crate::leanh::lean_ctor_get(v_p_5706_, 1);
                crate::leanh::lean_inc(v_k_5711_);
                crate::leanh::lean_dec_ref(v_p_5706_);
                v___x_5712_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5713_ = lean_nat_dec_eq(v_k_5711_, v___x_5712_);
                if v___x_5713_ == 0 {
                    let mut v___x_5714_: u8 = 0;
                    v___x_5714_ = lean_nat_dec_eq(v_k_5711_, v___x_5699_);
                    if v___x_5714_ == 0 {
                        let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5715_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5710_);
                        crate::leanh::lean_dec(v_x_5710_);
                        crate::leanh::lean_inc(v_npow_5709_);
                        v___x_5716_ =
                            crate::leanh::lean_apply_2(v_npow_5709_, v___x_5715_, v_k_5711_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5693_);
                        v___x_5717_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5693_,
                            v_ctx_5688_,
                            v_m_5707_,
                            v___x_5716_,
                        );
                        v___x_5718_ =
                            crate::leanh::lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5717_);
                        v___x_5719_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5687_,
                            v_ctx_5688_,
                            v_p_5696_,
                            v___x_5718_,
                        );
                        return v___x_5719_;
                    } else {
                        let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_k_5711_);
                        v___x_5720_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5710_);
                        crate::leanh::lean_dec(v_x_5710_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5693_);
                        v___x_5721_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5693_,
                            v_ctx_5688_,
                            v_m_5707_,
                            v___x_5720_,
                        );
                        v___x_5722_ =
                            crate::leanh::lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5721_);
                        v___x_5723_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5687_,
                            v_ctx_5688_,
                            v_p_5696_,
                            v___x_5722_,
                        );
                        return v___x_5723_;
                    }
                } else {
                    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5711_);
                    crate::leanh::lean_dec(v_x_5710_);
                    crate::leanh::lean_inc(v_ofNat_5708_);
                    v___x_5724_ = crate::leanh::lean_apply_1(v_ofNat_5708_, v___x_5699_);
                    crate::leanh::lean_inc_ref(v_toSemiring_5693_);
                    v___x_5725_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5693_,
                        v_ctx_5688_,
                        v_m_5707_,
                        v___x_5724_,
                    );
                    v___x_5726_ = crate::leanh::lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5725_);
                    v___x_5727_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                        v_inst_5687_,
                        v_ctx_5688_,
                        v_p_5696_,
                        v___x_5726_,
                    );
                    return v___x_5727_;
                }
            }
        } else {
            crate::leanh::lean_dec(v_zsmul_5698_);
            crate::leanh::lean_dec(v_k_5694_);
            if crate::leanh::lean_obj_tag(v_v_5695_) == 0 {
                let mut v_ofNat_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ofNat_5728_ = crate::leanh::lean_ctor_get(v_toSemiring_5693_, 3);
                crate::leanh::lean_inc(v_ofNat_5728_);
                v___x_5729_ = crate::leanh::lean_apply_1(v_ofNat_5728_, v___x_5699_);
                v___x_5730_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5687_,
                    v_ctx_5688_,
                    v_p_5696_,
                    v___x_5729_,
                );
                return v___x_5730_;
            } else {
                let mut v_p_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_m_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_npow_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5738_: u8 = 0;
                v_p_5731_ = crate::leanh::lean_ctor_get(v_v_5695_, 0);
                crate::leanh::lean_inc_ref(v_p_5731_);
                v_m_5732_ = crate::leanh::lean_ctor_get(v_v_5695_, 1);
                crate::leanh::lean_inc(v_m_5732_);
                crate::leanh::lean_dec_ref_known(v_v_5695_, 2);
                v_ofNat_5733_ = crate::leanh::lean_ctor_get(v_toSemiring_5693_, 3);
                v_npow_5734_ = crate::leanh::lean_ctor_get(v_toSemiring_5693_, 5);
                v_x_5735_ = crate::leanh::lean_ctor_get(v_p_5731_, 0);
                crate::leanh::lean_inc(v_x_5735_);
                v_k_5736_ = crate::leanh::lean_ctor_get(v_p_5731_, 1);
                crate::leanh::lean_inc(v_k_5736_);
                crate::leanh::lean_dec_ref(v_p_5731_);
                v___x_5737_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5738_ = lean_nat_dec_eq(v_k_5736_, v___x_5737_);
                if v___x_5738_ == 0 {
                    let mut v___x_5739_: u8 = 0;
                    v___x_5739_ = lean_nat_dec_eq(v_k_5736_, v___x_5699_);
                    if v___x_5739_ == 0 {
                        let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5740_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5735_);
                        crate::leanh::lean_dec(v_x_5735_);
                        crate::leanh::lean_inc(v_npow_5734_);
                        v___x_5741_ =
                            crate::leanh::lean_apply_2(v_npow_5734_, v___x_5740_, v_k_5736_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5693_);
                        v___x_5742_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5693_,
                            v_ctx_5688_,
                            v_m_5732_,
                            v___x_5741_,
                        );
                        v___x_5743_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5687_,
                            v_ctx_5688_,
                            v_p_5696_,
                            v___x_5742_,
                        );
                        return v___x_5743_;
                    } else {
                        let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_k_5736_);
                        v___x_5744_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5735_);
                        crate::leanh::lean_dec(v_x_5735_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5693_);
                        v___x_5745_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5693_,
                            v_ctx_5688_,
                            v_m_5732_,
                            v___x_5744_,
                        );
                        v___x_5746_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5687_,
                            v_ctx_5688_,
                            v_p_5696_,
                            v___x_5745_,
                        );
                        return v___x_5746_;
                    }
                } else {
                    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5736_);
                    crate::leanh::lean_dec(v_x_5735_);
                    crate::leanh::lean_inc(v_ofNat_5733_);
                    v___x_5747_ = crate::leanh::lean_apply_1(v_ofNat_5733_, v___x_5699_);
                    crate::leanh::lean_inc_ref(v_toSemiring_5693_);
                    v___x_5748_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5693_,
                        v_ctx_5688_,
                        v_m_5732_,
                        v___x_5747_,
                    );
                    v___x_5749_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                        v_inst_5687_,
                        v_ctx_5688_,
                        v_p_5696_,
                        v___x_5748_,
                    );
                    return v___x_5749_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(
    mut v_inst_5750_: *mut crate::leanh::LeanObject,
    mut v_ctx_5751_: *mut crate::leanh::LeanObject,
    mut v_p_5752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5753_ =
        l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_5750_, v_ctx_5751_, v_p_5752_);
    crate::leanh::lean_dec_ref(v_ctx_5751_);
    return v_res_5753_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27(
    mut v_00_u03b1_5754_: *mut crate::leanh::LeanObject,
    mut v_inst_5755_: *mut crate::leanh::LeanObject,
    mut v_ctx_5756_: *mut crate::leanh::LeanObject,
    mut v_p_5757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_5757_) == 0 {
        let mut v_intCast_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_intCast_5758_ = crate::leanh::lean_ctor_get(v_inst_5755_, 3);
        crate::leanh::lean_inc(v_intCast_5758_);
        crate::leanh::lean_dec_ref(v_inst_5755_);
        v_k_5759_ = crate::leanh::lean_ctor_get(v_p_5757_, 0);
        crate::leanh::lean_inc(v_k_5759_);
        crate::leanh::lean_dec_ref_known(v_p_5757_, 1);
        v___x_5760_ = crate::leanh::lean_apply_1(v_intCast_5758_, v_k_5759_);
        return v___x_5760_;
    } else {
        let mut v_toSemiring_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zsmul_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5769_: u8 = 0;
        v_toSemiring_5761_ = crate::leanh::lean_ctor_get(v_inst_5755_, 0);
        v_k_5762_ = crate::leanh::lean_ctor_get(v_p_5757_, 0);
        crate::leanh::lean_inc(v_k_5762_);
        v_v_5763_ = crate::leanh::lean_ctor_get(v_p_5757_, 1);
        crate::leanh::lean_inc(v_v_5763_);
        v_p_5764_ = crate::leanh::lean_ctor_get(v_p_5757_, 2);
        crate::leanh::lean_inc_ref(v_p_5764_);
        crate::leanh::lean_dec_ref_known(v_p_5757_, 3);
        crate::leanh::lean_inc_ref(v_inst_5755_);
        v___x_5765_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5755_);
        v_zsmul_5766_ = crate::leanh::lean_ctor_get(v___x_5765_, 2);
        crate::leanh::lean_inc(v_zsmul_5766_);
        crate::leanh::lean_dec_ref(v___x_5765_);
        v___x_5767_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5768_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_5769_ = lean_int_dec_eq(v_k_5762_, v___x_5768_);
        if v___x_5769_ == 0 {
            if crate::leanh::lean_obj_tag(v_v_5763_) == 0 {
                let mut v_ofNat_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ofNat_5770_ = crate::leanh::lean_ctor_get(v_toSemiring_5761_, 3);
                crate::leanh::lean_inc(v_ofNat_5770_);
                v___x_5771_ = crate::leanh::lean_apply_1(v_ofNat_5770_, v___x_5767_);
                v___x_5772_ = crate::leanh::lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5771_);
                v___x_5773_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5755_,
                    v_ctx_5756_,
                    v_p_5764_,
                    v___x_5772_,
                );
                return v___x_5773_;
            } else {
                let mut v_p_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_m_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_npow_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5781_: u8 = 0;
                v_p_5774_ = crate::leanh::lean_ctor_get(v_v_5763_, 0);
                crate::leanh::lean_inc_ref(v_p_5774_);
                v_m_5775_ = crate::leanh::lean_ctor_get(v_v_5763_, 1);
                crate::leanh::lean_inc(v_m_5775_);
                crate::leanh::lean_dec_ref_known(v_v_5763_, 2);
                v_ofNat_5776_ = crate::leanh::lean_ctor_get(v_toSemiring_5761_, 3);
                v_npow_5777_ = crate::leanh::lean_ctor_get(v_toSemiring_5761_, 5);
                v_x_5778_ = crate::leanh::lean_ctor_get(v_p_5774_, 0);
                crate::leanh::lean_inc(v_x_5778_);
                v_k_5779_ = crate::leanh::lean_ctor_get(v_p_5774_, 1);
                crate::leanh::lean_inc(v_k_5779_);
                crate::leanh::lean_dec_ref(v_p_5774_);
                v___x_5780_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5781_ = lean_nat_dec_eq(v_k_5779_, v___x_5780_);
                if v___x_5781_ == 0 {
                    let mut v___x_5782_: u8 = 0;
                    v___x_5782_ = lean_nat_dec_eq(v_k_5779_, v___x_5767_);
                    if v___x_5782_ == 0 {
                        let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5783_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5778_);
                        crate::leanh::lean_dec(v_x_5778_);
                        crate::leanh::lean_inc(v_npow_5777_);
                        v___x_5784_ =
                            crate::leanh::lean_apply_2(v_npow_5777_, v___x_5783_, v_k_5779_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5761_);
                        v___x_5785_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5761_,
                            v_ctx_5756_,
                            v_m_5775_,
                            v___x_5784_,
                        );
                        v___x_5786_ =
                            crate::leanh::lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5785_);
                        v___x_5787_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5755_,
                            v_ctx_5756_,
                            v_p_5764_,
                            v___x_5786_,
                        );
                        return v___x_5787_;
                    } else {
                        let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_k_5779_);
                        v___x_5788_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5778_);
                        crate::leanh::lean_dec(v_x_5778_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5761_);
                        v___x_5789_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5761_,
                            v_ctx_5756_,
                            v_m_5775_,
                            v___x_5788_,
                        );
                        v___x_5790_ =
                            crate::leanh::lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5789_);
                        v___x_5791_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5755_,
                            v_ctx_5756_,
                            v_p_5764_,
                            v___x_5790_,
                        );
                        return v___x_5791_;
                    }
                } else {
                    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5779_);
                    crate::leanh::lean_dec(v_x_5778_);
                    crate::leanh::lean_inc(v_ofNat_5776_);
                    v___x_5792_ = crate::leanh::lean_apply_1(v_ofNat_5776_, v___x_5767_);
                    crate::leanh::lean_inc_ref(v_toSemiring_5761_);
                    v___x_5793_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5761_,
                        v_ctx_5756_,
                        v_m_5775_,
                        v___x_5792_,
                    );
                    v___x_5794_ = crate::leanh::lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5793_);
                    v___x_5795_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                        v_inst_5755_,
                        v_ctx_5756_,
                        v_p_5764_,
                        v___x_5794_,
                    );
                    return v___x_5795_;
                }
            }
        } else {
            crate::leanh::lean_dec(v_zsmul_5766_);
            crate::leanh::lean_dec(v_k_5762_);
            if crate::leanh::lean_obj_tag(v_v_5763_) == 0 {
                let mut v_ofNat_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ofNat_5796_ = crate::leanh::lean_ctor_get(v_toSemiring_5761_, 3);
                crate::leanh::lean_inc(v_ofNat_5796_);
                v___x_5797_ = crate::leanh::lean_apply_1(v_ofNat_5796_, v___x_5767_);
                v___x_5798_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5755_,
                    v_ctx_5756_,
                    v_p_5764_,
                    v___x_5797_,
                );
                return v___x_5798_;
            } else {
                let mut v_p_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_m_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_npow_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5806_: u8 = 0;
                v_p_5799_ = crate::leanh::lean_ctor_get(v_v_5763_, 0);
                crate::leanh::lean_inc_ref(v_p_5799_);
                v_m_5800_ = crate::leanh::lean_ctor_get(v_v_5763_, 1);
                crate::leanh::lean_inc(v_m_5800_);
                crate::leanh::lean_dec_ref_known(v_v_5763_, 2);
                v_ofNat_5801_ = crate::leanh::lean_ctor_get(v_toSemiring_5761_, 3);
                v_npow_5802_ = crate::leanh::lean_ctor_get(v_toSemiring_5761_, 5);
                v_x_5803_ = crate::leanh::lean_ctor_get(v_p_5799_, 0);
                crate::leanh::lean_inc(v_x_5803_);
                v_k_5804_ = crate::leanh::lean_ctor_get(v_p_5799_, 1);
                crate::leanh::lean_inc(v_k_5804_);
                crate::leanh::lean_dec_ref(v_p_5799_);
                v___x_5805_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5806_ = lean_nat_dec_eq(v_k_5804_, v___x_5805_);
                if v___x_5806_ == 0 {
                    let mut v___x_5807_: u8 = 0;
                    v___x_5807_ = lean_nat_dec_eq(v_k_5804_, v___x_5767_);
                    if v___x_5807_ == 0 {
                        let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5808_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5803_);
                        crate::leanh::lean_dec(v_x_5803_);
                        crate::leanh::lean_inc(v_npow_5802_);
                        v___x_5809_ =
                            crate::leanh::lean_apply_2(v_npow_5802_, v___x_5808_, v_k_5804_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5761_);
                        v___x_5810_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5761_,
                            v_ctx_5756_,
                            v_m_5800_,
                            v___x_5809_,
                        );
                        v___x_5811_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5755_,
                            v_ctx_5756_,
                            v_p_5764_,
                            v___x_5810_,
                        );
                        return v___x_5811_;
                    } else {
                        let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_k_5804_);
                        v___x_5812_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5803_);
                        crate::leanh::lean_dec(v_x_5803_);
                        crate::leanh::lean_inc_ref(v_toSemiring_5761_);
                        v___x_5813_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5761_,
                            v_ctx_5756_,
                            v_m_5800_,
                            v___x_5812_,
                        );
                        v___x_5814_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5755_,
                            v_ctx_5756_,
                            v_p_5764_,
                            v___x_5813_,
                        );
                        return v___x_5814_;
                    }
                } else {
                    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_k_5804_);
                    crate::leanh::lean_dec(v_x_5803_);
                    crate::leanh::lean_inc(v_ofNat_5801_);
                    v___x_5815_ = crate::leanh::lean_apply_1(v_ofNat_5801_, v___x_5767_);
                    crate::leanh::lean_inc_ref(v_toSemiring_5761_);
                    v___x_5816_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5761_,
                        v_ctx_5756_,
                        v_m_5800_,
                        v___x_5815_,
                    );
                    v___x_5817_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                        v_inst_5755_,
                        v_ctx_5756_,
                        v_p_5764_,
                        v___x_5816_,
                    );
                    return v___x_5817_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27___boxed(
    mut v_00_u03b1_5818_: *mut crate::leanh::LeanObject,
    mut v_inst_5819_: *mut crate::leanh::LeanObject,
    mut v_ctx_5820_: *mut crate::leanh::LeanObject,
    mut v_p_5821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5822_ = l_Lean_Grind_CommRing_Poly_denote_x27(
        v_00_u03b1_5818_,
        v_inst_5819_,
        v_ctx_5820_,
        v_p_5821_,
    );
    crate::leanh::lean_dec_ref(v_ctx_5820_);
    return v_res_5822_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ofMon(
    mut v_m_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_5825_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_5826_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5826_, 0, v___x_5824_);
    crate::leanh::lean_ctor_set(v___x_5826_, 1, v_m_5823_);
    crate::leanh::lean_ctor_set(v___x_5826_, 2, v___x_5825_);
    return v___x_5826_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ofVar(
    mut v_x_5827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_5827_);
    v___x_5829_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_5828_);
    return v___x_5829_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_isSorted(
    mut v_x_5830_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5831_: u8 = 0;
    let mut v_p_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: u8 = 0;
    let mut v_v_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: u8 = 0;
    let mut v___x_5837_: u8 = 0;
    let mut v___x_5838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5830_) == 0 {
                    v___x_5831_ = 1;
                    return v___x_5831_;
                } else {
                    v_p_5832_ = crate::leanh::lean_ctor_get(v_x_5830_, 2);
                    if crate::leanh::lean_obj_tag(v_p_5832_) == 0 {
                        v___x_5833_ = 1;
                        return v___x_5833_;
                    } else {
                        v_v_5834_ = crate::leanh::lean_ctor_get(v_x_5830_, 1);
                        v_v_5835_ = crate::leanh::lean_ctor_get(v_p_5832_, 1);
                        v___x_5836_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_5834_, v_v_5835_);
                        v___x_5837_ = 2;
                        v___x_5838_ = l_instDecidableEqOrdering(v___x_5836_, v___x_5837_);
                        if v___x_5838_ == 0 {
                            return v___x_5838_;
                        } else {
                            v_x_5830_ = v_p_5832_;
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
pub unsafe fn l_Lean_Grind_CommRing_Poly_isSorted___boxed(
    mut v_x_5840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5841_: u8 = 0;
    let mut v_r_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5841_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_5840_);
    crate::leanh::lean_dec_ref(v_x_5840_);
    v_r_5842_ = crate::leanh::lean_box((v_res_5841_) as usize);
    return v_r_5842_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst_go(
    mut v_k_5843_: *mut crate::leanh::LeanObject,
    mut v_a_5844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5848_: u8 = 0;
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5853_: u8 = 0;
    let mut v_k_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5859_: u8 = 0;
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5844_) == 0 {
                    v_k_5845_ = crate::leanh::lean_ctor_get(v_a_5844_, 0);
                    v_isSharedCheck_5853_ = (!crate::leanh::lean_is_exclusive(v_a_5844_)) as u8;
                    if v_isSharedCheck_5853_ == 0 {
                        v___x_5847_ = v_a_5844_;
                        v_isShared_5848_ = v_isSharedCheck_5853_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5845_);
                        crate::leanh::lean_dec(v_a_5844_);
                        v___x_5847_ = crate::leanh::lean_box(0);
                        v_isShared_5848_ = v_isSharedCheck_5853_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5854_ = crate::leanh::lean_ctor_get(v_a_5844_, 0);
                    v_v_5855_ = crate::leanh::lean_ctor_get(v_a_5844_, 1);
                    v_p_5856_ = crate::leanh::lean_ctor_get(v_a_5844_, 2);
                    v_isSharedCheck_5864_ = (!crate::leanh::lean_is_exclusive(v_a_5844_)) as u8;
                    if v_isSharedCheck_5864_ == 0 {
                        v___x_5858_ = v_a_5844_;
                        v_isShared_5859_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_5856_);
                        crate::leanh::lean_inc(v_v_5855_);
                        crate::leanh::lean_inc(v_k_5854_);
                        crate::leanh::lean_dec(v_a_5844_);
                        v___x_5858_ = crate::leanh::lean_box(0);
                        v_isShared_5859_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5849_ = lean_int_add(v_k_5845_, v_k_5843_);
                crate::leanh::lean_dec(v_k_5845_);
                if v_isShared_5848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5847_, 0, v___x_5849_);
                    v___x_5851_ = v___x_5847_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5849_);
                    v___x_5851_ = v_reuseFailAlloc_5852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5851_;
            }
            3 => {
                v___x_5860_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_5843_, v_p_5856_);
                if v_isShared_5859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5858_, 2, v___x_5860_);
                    v___x_5862_ = v___x_5858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_k_5854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 1, v_v_5855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 2, v___x_5860_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst_go___boxed(
    mut v_k_5865_: *mut crate::leanh::LeanObject,
    mut v_a_5866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5867_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_5865_, v_a_5866_);
    crate::leanh::lean_dec(v_k_5865_);
    return v_res_5867_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst(
    mut v_p_5868_: *mut crate::leanh::LeanObject,
    mut v_k_5869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: u8 = 0;
    v___x_5870_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5871_ = lean_int_dec_eq(v_k_5869_, v___x_5870_);
    if v___x_5871_ == 0 {
        let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5872_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_5869_, v_p_5868_);
        return v___x_5872_;
    } else {
        return v_p_5868_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst___boxed(
    mut v_p_5873_: *mut crate::leanh::LeanObject,
    mut v_k_5874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5875_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_5873_, v_k_5874_);
    crate::leanh::lean_dec(v_k_5874_);
    return v_res_5875_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(
    mut v_p_5876_: *mut crate::leanh::LeanObject,
    mut v_h__1_5877_: *mut crate::leanh::LeanObject,
    mut v_h__2_5878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_5876_) == 0 {
        let mut v_k_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5878_);
        v_k_5879_ = crate::leanh::lean_ctor_get(v_p_5876_, 0);
        crate::leanh::lean_inc(v_k_5879_);
        crate::leanh::lean_dec_ref_known(v_p_5876_, 1);
        v___x_5880_ = crate::leanh::lean_apply_1(v_h__1_5877_, v_k_5879_);
        return v___x_5880_;
    } else {
        let mut v_k_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5877_);
        v_k_5881_ = crate::leanh::lean_ctor_get(v_p_5876_, 0);
        crate::leanh::lean_inc(v_k_5881_);
        v_v_5882_ = crate::leanh::lean_ctor_get(v_p_5876_, 1);
        crate::leanh::lean_inc(v_v_5882_);
        v_p_5883_ = crate::leanh::lean_ctor_get(v_p_5876_, 2);
        crate::leanh::lean_inc_ref(v_p_5883_);
        crate::leanh::lean_dec_ref_known(v_p_5876_, 3);
        v___x_5884_ = crate::leanh::lean_apply_3(v_h__2_5878_, v_k_5881_, v_v_5882_, v_p_5883_);
        return v___x_5884_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(
    mut v_motive_5885_: *mut crate::leanh::LeanObject,
    mut v_p_5886_: *mut crate::leanh::LeanObject,
    mut v_h__1_5887_: *mut crate::leanh::LeanObject,
    mut v_h__2_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_5886_) == 0 {
        let mut v_k_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5888_);
        v_k_5889_ = crate::leanh::lean_ctor_get(v_p_5886_, 0);
        crate::leanh::lean_inc(v_k_5889_);
        crate::leanh::lean_dec_ref_known(v_p_5886_, 1);
        v___x_5890_ = crate::leanh::lean_apply_1(v_h__1_5887_, v_k_5889_);
        return v___x_5890_;
    } else {
        let mut v_k_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5887_);
        v_k_5891_ = crate::leanh::lean_ctor_get(v_p_5886_, 0);
        crate::leanh::lean_inc(v_k_5891_);
        v_v_5892_ = crate::leanh::lean_ctor_get(v_p_5886_, 1);
        crate::leanh::lean_inc(v_v_5892_);
        v_p_5893_ = crate::leanh::lean_ctor_get(v_p_5886_, 2);
        crate::leanh::lean_inc_ref(v_p_5893_);
        crate::leanh::lean_dec_ref_known(v_p_5886_, 3);
        v___x_5894_ = crate::leanh::lean_apply_3(v_h__2_5888_, v_k_5891_, v_v_5892_, v_p_5893_);
        return v___x_5894_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insert_go(
    mut v_k_5895_: *mut crate::leanh::LeanObject,
    mut v_m_5896_: *mut crate::leanh::LeanObject,
    mut v_a_5897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: u8 = 0;
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5910_: u8 = 0;
    let mut v_unused_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v_k_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut v_unused_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5897_) == 0 {
                    v___x_5898_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5898_, 0, v_k_5895_);
                    crate::leanh::lean_ctor_set(v___x_5898_, 1, v_m_5896_);
                    crate::leanh::lean_ctor_set(v___x_5898_, 2, v_a_5897_);
                    return v___x_5898_;
                } else {
                    v_k_5899_ = crate::leanh::lean_ctor_get(v_a_5897_, 0);
                    v_v_5900_ = crate::leanh::lean_ctor_get(v_a_5897_, 1);
                    v_p_5901_ = crate::leanh::lean_ctor_get(v_a_5897_, 2);
                    v___x_5902_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_5896_, v_v_5900_);
                    match v___x_5902_ {
                        0 => {
                            crate::leanh::lean_inc_ref(v_p_5901_);
                            crate::leanh::lean_inc(v_v_5900_);
                            crate::leanh::lean_inc(v_k_5899_);
                            v_isSharedCheck_5910_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5897_)) as u8;
                            if v_isSharedCheck_5910_ == 0 {
                                v_unused_5911_ = crate::leanh::lean_ctor_get(v_a_5897_, 2);
                                crate::leanh::lean_dec(v_unused_5911_);
                                v_unused_5912_ = crate::leanh::lean_ctor_get(v_a_5897_, 1);
                                crate::leanh::lean_dec(v_unused_5912_);
                                v_unused_5913_ = crate::leanh::lean_ctor_get(v_a_5897_, 0);
                                crate::leanh::lean_dec(v_unused_5913_);
                                v___x_5904_ = v_a_5897_;
                                v_isShared_5905_ = v_isSharedCheck_5910_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5897_);
                                v___x_5904_ = crate::leanh::lean_box(0);
                                v_isShared_5905_ = v_isSharedCheck_5910_;
                                state = 1;
                                continue;
                            }
                        }
                        1 => {
                            crate::leanh::lean_inc_ref(v_p_5901_);
                            crate::leanh::lean_inc(v_k_5899_);
                            v_isSharedCheck_5923_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5897_)) as u8;
                            if v_isSharedCheck_5923_ == 0 {
                                v_unused_5924_ = crate::leanh::lean_ctor_get(v_a_5897_, 2);
                                crate::leanh::lean_dec(v_unused_5924_);
                                v_unused_5925_ = crate::leanh::lean_ctor_get(v_a_5897_, 1);
                                crate::leanh::lean_dec(v_unused_5925_);
                                v_unused_5926_ = crate::leanh::lean_ctor_get(v_a_5897_, 0);
                                crate::leanh::lean_dec(v_unused_5926_);
                                v___x_5915_ = v_a_5897_;
                                v_isShared_5916_ = v_isSharedCheck_5923_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5897_);
                                v___x_5915_ = crate::leanh::lean_box(0);
                                v_isShared_5916_ = v_isSharedCheck_5923_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            v___x_5927_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5927_, 0, v_k_5895_);
                            crate::leanh::lean_ctor_set(v___x_5927_, 1, v_m_5896_);
                            crate::leanh::lean_ctor_set(v___x_5927_, 2, v_a_5897_);
                            return v___x_5927_;
                        }
                    }
                }
            }
            1 => {
                v___x_5906_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_5895_, v_m_5896_, v_p_5901_);
                if v_isShared_5905_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5904_, 2, v___x_5906_);
                    v___x_5908_ = v___x_5904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5909_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_k_5899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5909_, 1, v_v_5900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5909_, 2, v___x_5906_);
                    v___x_5908_ = v_reuseFailAlloc_5909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5908_;
            }
            3 => {
                v_k_5917_ = lean_int_add(v_k_5895_, v_k_5899_);
                crate::leanh::lean_dec(v_k_5899_);
                crate::leanh::lean_dec(v_k_5895_);
                v___x_5918_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_5919_ = lean_int_dec_eq(v_k_5917_, v___x_5918_);
                if v___x_5919_ == 0 {
                    if v_isShared_5916_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5915_, 1, v_m_5896_);
                        crate::leanh::lean_ctor_set(v___x_5915_, 0, v_k_5917_);
                        v___x_5921_ = v___x_5915_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5922_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_k_5917_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 1, v_m_5896_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 2, v_p_5901_);
                        v___x_5921_ = v_reuseFailAlloc_5922_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_5917_);
                    crate::leanh::lean_del_object(v___x_5915_);
                    crate::leanh::lean_dec(v_m_5896_);
                    return v_p_5901_;
                }
            }
            4 => {
                return v___x_5921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insert(
    mut v_k_5928_: *mut crate::leanh::LeanObject,
    mut v_m_5929_: *mut crate::leanh::LeanObject,
    mut v_p_5930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: u8 = 0;
    v___x_5931_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5932_ = lean_int_dec_eq(v_k_5928_, v___x_5931_);
    if v___x_5932_ == 0 {
        let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5934_: u8 = 0;
        v___x_5933_ = crate::leanh::lean_box(0);
        v___x_5934_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_5929_, v___x_5933_);
        if v___x_5934_ == 0 {
            let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5935_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_5928_, v_m_5929_, v_p_5930_);
            return v___x_5935_;
        } else {
            let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_m_5929_);
            v___x_5936_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_5930_, v_k_5928_);
            crate::leanh::lean_dec(v_k_5928_);
            return v___x_5936_;
        }
    } else {
        crate::leanh::lean_dec(v_m_5929_);
        crate::leanh::lean_dec(v_k_5928_);
        return v_p_5930_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_concat(
    mut v_p_u2081_5937_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_5938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5946_: u8 = 0;
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_5937_) == 0 {
                    v_k_5939_ = crate::leanh::lean_ctor_get(v_p_u2081_5937_, 0);
                    crate::leanh::lean_inc(v_k_5939_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_5937_, 1);
                    v___x_5940_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_5938_, v_k_5939_);
                    crate::leanh::lean_dec(v_k_5939_);
                    return v___x_5940_;
                } else {
                    v_k_5941_ = crate::leanh::lean_ctor_get(v_p_u2081_5937_, 0);
                    v_v_5942_ = crate::leanh::lean_ctor_get(v_p_u2081_5937_, 1);
                    v_p_5943_ = crate::leanh::lean_ctor_get(v_p_u2081_5937_, 2);
                    v_isSharedCheck_5951_ =
                        (!crate::leanh::lean_is_exclusive(v_p_u2081_5937_)) as u8;
                    if v_isSharedCheck_5951_ == 0 {
                        v___x_5945_ = v_p_u2081_5937_;
                        v_isShared_5946_ = v_isSharedCheck_5951_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_5943_);
                        crate::leanh::lean_inc(v_v_5942_);
                        crate::leanh::lean_inc(v_k_5941_);
                        crate::leanh::lean_dec(v_p_u2081_5937_);
                        v___x_5945_ = crate::leanh::lean_box(0);
                        v_isShared_5946_ = v_isSharedCheck_5951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5947_ = l_Lean_Grind_CommRing_Poly_concat(v_p_5943_, v_p_u2082_5938_);
                if v_isShared_5946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5945_, 2, v___x_5947_);
                    v___x_5949_ = v___x_5945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_k_5941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 1, v_v_5942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 2, v___x_5947_);
                    v___x_5949_ = v_reuseFailAlloc_5950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst_go(
    mut v_k_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut v_k_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5968_: u8 = 0;
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5953_) == 0 {
                    v_k_5954_ = crate::leanh::lean_ctor_get(v_a_5953_, 0);
                    v_isSharedCheck_5962_ = (!crate::leanh::lean_is_exclusive(v_a_5953_)) as u8;
                    if v_isSharedCheck_5962_ == 0 {
                        v___x_5956_ = v_a_5953_;
                        v_isShared_5957_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5954_);
                        crate::leanh::lean_dec(v_a_5953_);
                        v___x_5956_ = crate::leanh::lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5963_ = crate::leanh::lean_ctor_get(v_a_5953_, 0);
                    v_v_5964_ = crate::leanh::lean_ctor_get(v_a_5953_, 1);
                    v_p_5965_ = crate::leanh::lean_ctor_get(v_a_5953_, 2);
                    v_isSharedCheck_5974_ = (!crate::leanh::lean_is_exclusive(v_a_5953_)) as u8;
                    if v_isSharedCheck_5974_ == 0 {
                        v___x_5967_ = v_a_5953_;
                        v_isShared_5968_ = v_isSharedCheck_5974_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_5965_);
                        crate::leanh::lean_inc(v_v_5964_);
                        crate::leanh::lean_inc(v_k_5963_);
                        crate::leanh::lean_dec(v_a_5953_);
                        v___x_5967_ = crate::leanh::lean_box(0);
                        v_isShared_5968_ = v_isSharedCheck_5974_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5958_ = lean_int_mul(v_k_5952_, v_k_5954_);
                crate::leanh::lean_dec(v_k_5954_);
                if v_isShared_5957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5956_, 0, v___x_5958_);
                    v___x_5960_ = v___x_5956_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5958_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5960_;
            }
            3 => {
                v___x_5969_ = lean_int_mul(v_k_5952_, v_k_5963_);
                crate::leanh::lean_dec(v_k_5963_);
                v___x_5970_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_5952_, v_p_5965_);
                if v_isShared_5968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5967_, 2, v___x_5970_);
                    crate::leanh::lean_ctor_set(v___x_5967_, 0, v___x_5969_);
                    v___x_5972_ = v___x_5967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5973_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5973_, 0, v___x_5969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5973_, 1, v_v_5964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5973_, 2, v___x_5970_);
                    v___x_5972_ = v_reuseFailAlloc_5973_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(
    mut v_k_5975_: *mut crate::leanh::LeanObject,
    mut v_a_5976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5977_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_5975_, v_a_5976_);
    crate::leanh::lean_dec(v_k_5975_);
    return v_res_5977_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst(
    mut v_k_5978_: *mut crate::leanh::LeanObject,
    mut v_p_5979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    v___x_5980_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5981_ = lean_int_dec_eq(v_k_5978_, v___x_5980_);
    if v___x_5981_ == 0 {
        let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5983_: u8 = 0;
        v___x_5982_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_5983_ = lean_int_dec_eq(v_k_5978_, v___x_5982_);
        if v___x_5983_ == 0 {
            let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5984_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_5978_, v_p_5979_);
            return v___x_5984_;
        } else {
            return v_p_5979_;
        }
    } else {
        let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_5979_);
        v___x_5985_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
        );
        return v___x_5985_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst___boxed(
    mut v_k_5986_: *mut crate::leanh::LeanObject,
    mut v_p_5987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5988_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_5986_, v_p_5987_);
    crate::leanh::lean_dec(v_k_5986_);
    return v_res_5988_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_go(
    mut v_k_5989_: *mut crate::leanh::LeanObject,
    mut v_m_5990_: *mut crate::leanh::LeanObject,
    mut v_a_5991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: u8 = 0;
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5991_) == 0 {
                    v_k_5992_ = crate::leanh::lean_ctor_get(v_a_5991_, 0);
                    crate::leanh::lean_inc(v_k_5992_);
                    crate::leanh::lean_dec_ref_known(v_a_5991_, 1);
                    v___x_5993_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v___x_5994_ = lean_int_dec_eq(v_k_5992_, v___x_5993_);
                    if v___x_5994_ == 0 {
                        v___x_5995_ = lean_int_mul(v_k_5989_, v_k_5992_);
                        crate::leanh::lean_dec(v_k_5992_);
                        v___x_5996_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        v___x_5997_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5997_, 0, v___x_5995_);
                        crate::leanh::lean_ctor_set(v___x_5997_, 1, v_m_5990_);
                        crate::leanh::lean_ctor_set(v___x_5997_, 2, v___x_5996_);
                        return v___x_5997_;
                    } else {
                        crate::leanh::lean_dec(v_k_5992_);
                        crate::leanh::lean_dec(v_m_5990_);
                        v___x_5998_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        return v___x_5998_;
                    }
                } else {
                    v_k_5999_ = crate::leanh::lean_ctor_get(v_a_5991_, 0);
                    v_v_6000_ = crate::leanh::lean_ctor_get(v_a_5991_, 1);
                    v_p_6001_ = crate::leanh::lean_ctor_get(v_a_5991_, 2);
                    v_isSharedCheck_6011_ = (!crate::leanh::lean_is_exclusive(v_a_5991_)) as u8;
                    if v_isSharedCheck_6011_ == 0 {
                        v___x_6003_ = v_a_5991_;
                        v_isShared_6004_ = v_isSharedCheck_6011_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_6001_);
                        crate::leanh::lean_inc(v_v_6000_);
                        crate::leanh::lean_inc(v_k_5999_);
                        crate::leanh::lean_dec(v_a_5991_);
                        v___x_6003_ = crate::leanh::lean_box(0);
                        v_isShared_6004_ = v_isSharedCheck_6011_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6005_ = lean_int_mul(v_k_5989_, v_k_5999_);
                crate::leanh::lean_dec(v_k_5999_);
                crate::leanh::lean_inc(v_m_5990_);
                v___x_6006_ = l_Lean_Grind_CommRing_Mon_mul(v_m_5990_, v_v_6000_);
                v___x_6007_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_5989_, v_m_5990_, v_p_6001_);
                if v_isShared_6004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6003_, 2, v___x_6007_);
                    crate::leanh::lean_ctor_set(v___x_6003_, 1, v___x_6006_);
                    crate::leanh::lean_ctor_set(v___x_6003_, 0, v___x_6005_);
                    v___x_6009_ = v___x_6003_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6010_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6010_, 0, v___x_6005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6010_, 1, v___x_6006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6010_, 2, v___x_6007_);
                    v___x_6009_ = v_reuseFailAlloc_6010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(
    mut v_k_6012_: *mut crate::leanh::LeanObject,
    mut v_m_6013_: *mut crate::leanh::LeanObject,
    mut v_a_6014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6015_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_6012_, v_m_6013_, v_a_6014_);
    crate::leanh::lean_dec(v_k_6012_);
    return v_res_6015_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon(
    mut v_k_6016_: *mut crate::leanh::LeanObject,
    mut v_m_6017_: *mut crate::leanh::LeanObject,
    mut v_p_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: u8 = 0;
    v___x_6019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6020_ = lean_int_dec_eq(v_k_6016_, v___x_6019_);
    if v___x_6020_ == 0 {
        let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6022_: u8 = 0;
        v___x_6021_ = crate::leanh::lean_box(0);
        v___x_6022_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6017_, v___x_6021_);
        if v___x_6022_ == 0 {
            let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6023_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_6016_, v_m_6017_, v_p_6018_);
            return v___x_6023_;
        } else {
            let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_m_6017_);
            v___x_6024_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6016_, v_p_6018_);
            return v___x_6024_;
        }
    } else {
        let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_6018_);
        crate::leanh::lean_dec(v_m_6017_);
        v___x_6025_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
        );
        return v___x_6025_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon___boxed(
    mut v_k_6026_: *mut crate::leanh::LeanObject,
    mut v_m_6027_: *mut crate::leanh::LeanObject,
    mut v_p_6028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6029_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_6026_, v_m_6027_, v_p_6028_);
    crate::leanh::lean_dec(v_k_6026_);
    return v_res_6029_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon__nc_go(
    mut v_k_6030_: *mut crate::leanh::LeanObject,
    mut v_m_6031_: *mut crate::leanh::LeanObject,
    mut v_p_6032_: *mut crate::leanh::LeanObject,
    mut v_acc_6033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_6032_) == 0 {
                    v_k_6034_ = crate::leanh::lean_ctor_get(v_p_6032_, 0);
                    crate::leanh::lean_inc(v_k_6034_);
                    crate::leanh::lean_dec_ref_known(v_p_6032_, 1);
                    v___x_6035_ = lean_int_mul(v_k_6030_, v_k_6034_);
                    crate::leanh::lean_dec(v_k_6034_);
                    v___x_6036_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6035_, v_m_6031_, v_acc_6033_);
                    return v___x_6036_;
                } else {
                    v_k_6037_ = crate::leanh::lean_ctor_get(v_p_6032_, 0);
                    crate::leanh::lean_inc(v_k_6037_);
                    v_v_6038_ = crate::leanh::lean_ctor_get(v_p_6032_, 1);
                    crate::leanh::lean_inc(v_v_6038_);
                    v_p_6039_ = crate::leanh::lean_ctor_get(v_p_6032_, 2);
                    crate::leanh::lean_inc_ref(v_p_6039_);
                    crate::leanh::lean_dec_ref_known(v_p_6032_, 3);
                    v___x_6040_ = lean_int_mul(v_k_6030_, v_k_6037_);
                    crate::leanh::lean_dec(v_k_6037_);
                    crate::leanh::lean_inc(v_m_6031_);
                    v___x_6041_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_6031_, v_v_6038_);
                    v___x_6042_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6040_, v___x_6041_, v_acc_6033_);
                    v_p_6032_ = v_p_6039_;
                    v_acc_6033_ = v___x_6042_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(
    mut v_k_6044_: *mut crate::leanh::LeanObject,
    mut v_m_6045_: *mut crate::leanh::LeanObject,
    mut v_p_6046_: *mut crate::leanh::LeanObject,
    mut v_acc_6047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6048_ =
        l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_6044_, v_m_6045_, v_p_6046_, v_acc_6047_);
    crate::leanh::lean_dec(v_k_6044_);
    return v_res_6048_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon__nc(
    mut v_k_6049_: *mut crate::leanh::LeanObject,
    mut v_m_6050_: *mut crate::leanh::LeanObject,
    mut v_p_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: u8 = 0;
    v___x_6052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6053_ = lean_int_dec_eq(v_k_6049_, v___x_6052_);
    if v___x_6053_ == 0 {
        let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6055_: u8 = 0;
        v___x_6054_ = crate::leanh::lean_box(0);
        v___x_6055_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6050_, v___x_6054_);
        if v___x_6055_ == 0 {
            let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6056_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                ),
                _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
            );
            v___x_6057_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(
                v_k_6049_,
                v_m_6050_,
                v_p_6051_,
                v___x_6056_,
            );
            return v___x_6057_;
        } else {
            let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_m_6050_);
            v___x_6058_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6049_, v_p_6051_);
            return v___x_6058_;
        }
    } else {
        let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_6051_);
        crate::leanh::lean_dec(v_m_6050_);
        v___x_6059_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
        );
        return v___x_6059_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(
    mut v_k_6060_: *mut crate::leanh::LeanObject,
    mut v_m_6061_: *mut crate::leanh::LeanObject,
    mut v_p_6062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6063_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_6060_, v_m_6061_, v_p_6062_);
    crate::leanh::lean_dec(v_k_6060_);
    return v_res_6063_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combine_go(
    mut v_fuel_6064_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_6065_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6068_: u8 = 0;
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6074_: u8 = 0;
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6079_: u8 = 0;
    let mut v_k_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: u8 = 0;
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6100_: u8 = 0;
    let mut v_unused_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6106_: u8 = 0;
    let mut v_k_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: u8 = 0;
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6115_: u8 = 0;
    let mut v_unused_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut v_unused_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6067_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_6068_ = lean_nat_dec_eq(v_fuel_6064_, v_zero_6067_);
                if v_isZero_6068_ == 1 {
                    crate::leanh::lean_dec(v_fuel_6064_);
                    v___x_6069_ =
                        l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_6065_, v_p_u2082_6066_);
                    return v___x_6069_;
                } else {
                    if crate::leanh::lean_obj_tag(v_p_u2081_6065_) == 0 {
                        crate::leanh::lean_dec(v_fuel_6064_);
                        if crate::leanh::lean_obj_tag(v_p_u2082_6066_) == 0 {
                            v_k_6070_ = crate::leanh::lean_ctor_get(v_p_u2081_6065_, 0);
                            crate::leanh::lean_inc(v_k_6070_);
                            crate::leanh::lean_dec_ref_known(v_p_u2081_6065_, 1);
                            v_k_6071_ = crate::leanh::lean_ctor_get(v_p_u2082_6066_, 0);
                            v_isSharedCheck_6079_ =
                                (!crate::leanh::lean_is_exclusive(v_p_u2082_6066_)) as u8;
                            if v_isSharedCheck_6079_ == 0 {
                                v___x_6073_ = v_p_u2082_6066_;
                                v_isShared_6074_ = v_isSharedCheck_6079_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_6071_);
                                crate::leanh::lean_dec(v_p_u2082_6066_);
                                v___x_6073_ = crate::leanh::lean_box(0);
                                v_isShared_6074_ = v_isSharedCheck_6079_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_k_6080_ = crate::leanh::lean_ctor_get(v_p_u2081_6065_, 0);
                            crate::leanh::lean_inc(v_k_6080_);
                            crate::leanh::lean_dec_ref_known(v_p_u2081_6065_, 1);
                            v___x_6081_ =
                                l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_6066_, v_k_6080_);
                            crate::leanh::lean_dec(v_k_6080_);
                            return v___x_6081_;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_p_u2082_6066_) == 0 {
                            crate::leanh::lean_dec(v_fuel_6064_);
                            v_k_6082_ = crate::leanh::lean_ctor_get(v_p_u2082_6066_, 0);
                            crate::leanh::lean_inc(v_k_6082_);
                            crate::leanh::lean_dec_ref_known(v_p_u2082_6066_, 1);
                            v___x_6083_ =
                                l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_6065_, v_k_6082_);
                            crate::leanh::lean_dec(v_k_6082_);
                            return v___x_6083_;
                        } else {
                            v_k_6084_ = crate::leanh::lean_ctor_get(v_p_u2081_6065_, 0);
                            v_v_6085_ = crate::leanh::lean_ctor_get(v_p_u2081_6065_, 1);
                            v_p_6086_ = crate::leanh::lean_ctor_get(v_p_u2081_6065_, 2);
                            v_k_6087_ = crate::leanh::lean_ctor_get(v_p_u2082_6066_, 0);
                            v_v_6088_ = crate::leanh::lean_ctor_get(v_p_u2082_6066_, 1);
                            v_p_6089_ = crate::leanh::lean_ctor_get(v_p_u2082_6066_, 2);
                            v_one_6090_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_n_6091_ = lean_nat_sub(v_fuel_6064_, v_one_6090_);
                            crate::leanh::lean_dec(v_fuel_6064_);
                            v___x_6092_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_6085_, v_v_6088_);
                            match v___x_6092_ {
                                0 => {
                                    crate::leanh::lean_inc_ref(v_p_6089_);
                                    crate::leanh::lean_inc(v_v_6088_);
                                    crate::leanh::lean_inc(v_k_6087_);
                                    v_isSharedCheck_6100_ =
                                        (!crate::leanh::lean_is_exclusive(v_p_u2082_6066_)) as u8;
                                    if v_isSharedCheck_6100_ == 0 {
                                        v_unused_6101_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_6066_, 2);
                                        crate::leanh::lean_dec(v_unused_6101_);
                                        v_unused_6102_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_6066_, 1);
                                        crate::leanh::lean_dec(v_unused_6102_);
                                        v_unused_6103_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_6066_, 0);
                                        crate::leanh::lean_dec(v_unused_6103_);
                                        v___x_6094_ = v_p_u2082_6066_;
                                        v_isShared_6095_ = v_isSharedCheck_6100_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_p_u2082_6066_);
                                        v___x_6094_ = crate::leanh::lean_box(0);
                                        v_isShared_6095_ = v_isSharedCheck_6100_;
                                        state = 3;
                                        continue;
                                    }
                                }
                                1 => {
                                    crate::leanh::lean_inc_ref(v_p_6089_);
                                    crate::leanh::lean_inc(v_k_6087_);
                                    crate::leanh::lean_inc_ref(v_p_6086_);
                                    crate::leanh::lean_inc(v_v_6085_);
                                    crate::leanh::lean_inc(v_k_6084_);
                                    crate::leanh::lean_dec_ref_known(v_p_u2081_6065_, 3);
                                    v_isSharedCheck_6115_ =
                                        (!crate::leanh::lean_is_exclusive(v_p_u2082_6066_)) as u8;
                                    if v_isSharedCheck_6115_ == 0 {
                                        v_unused_6116_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_6066_, 2);
                                        crate::leanh::lean_dec(v_unused_6116_);
                                        v_unused_6117_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_6066_, 1);
                                        crate::leanh::lean_dec(v_unused_6117_);
                                        v_unused_6118_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_6066_, 0);
                                        crate::leanh::lean_dec(v_unused_6118_);
                                        v___x_6105_ = v_p_u2082_6066_;
                                        v_isShared_6106_ = v_isSharedCheck_6115_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_p_u2082_6066_);
                                        v___x_6105_ = crate::leanh::lean_box(0);
                                        v_isShared_6106_ = v_isSharedCheck_6115_;
                                        state = 5;
                                        continue;
                                    }
                                }
                                _ => {
                                    crate::leanh::lean_inc_ref(v_p_6086_);
                                    crate::leanh::lean_inc(v_v_6085_);
                                    crate::leanh::lean_inc(v_k_6084_);
                                    v_isSharedCheck_6126_ =
                                        (!crate::leanh::lean_is_exclusive(v_p_u2081_6065_)) as u8;
                                    if v_isSharedCheck_6126_ == 0 {
                                        v_unused_6127_ =
                                            crate::leanh::lean_ctor_get(v_p_u2081_6065_, 2);
                                        crate::leanh::lean_dec(v_unused_6127_);
                                        v_unused_6128_ =
                                            crate::leanh::lean_ctor_get(v_p_u2081_6065_, 1);
                                        crate::leanh::lean_dec(v_unused_6128_);
                                        v_unused_6129_ =
                                            crate::leanh::lean_ctor_get(v_p_u2081_6065_, 0);
                                        crate::leanh::lean_dec(v_unused_6129_);
                                        v___x_6120_ = v_p_u2081_6065_;
                                        v_isShared_6121_ = v_isSharedCheck_6126_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_p_u2081_6065_);
                                        v___x_6120_ = crate::leanh::lean_box(0);
                                        v_isShared_6121_ = v_isSharedCheck_6126_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6075_ = lean_int_add(v_k_6070_, v_k_6071_);
                crate::leanh::lean_dec(v_k_6071_);
                crate::leanh::lean_dec(v_k_6070_);
                if v_isShared_6074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6073_, 0, v___x_6075_);
                    v___x_6077_ = v___x_6073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6075_);
                    v___x_6077_ = v_reuseFailAlloc_6078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6077_;
            }
            3 => {
                v___x_6096_ =
                    l_Lean_Grind_CommRing_Poly_combine_go(v_n_6091_, v_p_u2081_6065_, v_p_6089_);
                if v_isShared_6095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6094_, 2, v___x_6096_);
                    v___x_6098_ = v___x_6094_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6099_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6099_, 0, v_k_6087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6099_, 1, v_v_6088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6099_, 2, v___x_6096_);
                    v___x_6098_ = v_reuseFailAlloc_6099_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6098_;
            }
            5 => {
                v_k_6107_ = lean_int_add(v_k_6084_, v_k_6087_);
                crate::leanh::lean_dec(v_k_6087_);
                crate::leanh::lean_dec(v_k_6084_);
                v___x_6108_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6109_ = lean_int_dec_eq(v_k_6107_, v___x_6108_);
                if v___x_6109_ == 0 {
                    v___x_6110_ =
                        l_Lean_Grind_CommRing_Poly_combine_go(v_n_6091_, v_p_6086_, v_p_6089_);
                    if v_isShared_6106_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6105_, 2, v___x_6110_);
                        crate::leanh::lean_ctor_set(v___x_6105_, 1, v_v_6085_);
                        crate::leanh::lean_ctor_set(v___x_6105_, 0, v_k_6107_);
                        v___x_6112_ = v___x_6105_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6113_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_k_6107_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6113_, 1, v_v_6085_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6113_, 2, v___x_6110_);
                        v___x_6112_ = v_reuseFailAlloc_6113_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6107_);
                    crate::leanh::lean_del_object(v___x_6105_);
                    crate::leanh::lean_dec(v_v_6085_);
                    v_fuel_6064_ = v_n_6091_;
                    v_p_u2081_6065_ = v_p_6086_;
                    v_p_u2082_6066_ = v_p_6089_;
                    state = 0;
                    continue;
                }
            }
            6 => {
                return v___x_6112_;
            }
            7 => {
                v___x_6122_ =
                    l_Lean_Grind_CommRing_Poly_combine_go(v_n_6091_, v_p_6086_, v_p_u2082_6066_);
                if v_isShared_6121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6120_, 2, v___x_6122_);
                    v___x_6124_ = v___x_6120_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6125_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_k_6084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6125_, 1, v_v_6085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6125_, 2, v___x_6122_);
                    v___x_6124_ = v_reuseFailAlloc_6125_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combine(
    mut v_p_u2081_6130_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6132_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_6133_ =
        l_Lean_Grind_CommRing_Poly_combine_go(v___x_6132_, v_p_u2081_6130_, v_p_u2082_6131_);
    return v___x_6133_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(
    mut v_p_u2081_6134_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6135_: *mut crate::leanh::LeanObject,
    mut v_h__1_6136_: *mut crate::leanh::LeanObject,
    mut v_h__2_6137_: *mut crate::leanh::LeanObject,
    mut v_h__3_6138_: *mut crate::leanh::LeanObject,
    mut v_h__4_6139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_6134_) == 0 {
        crate::leanh::lean_dec(v_h__4_6139_);
        crate::leanh::lean_dec(v_h__3_6138_);
        if crate::leanh::lean_obj_tag(v_p_u2082_6135_) == 0 {
            let mut v_k_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_6137_);
            v_k_6140_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 0);
            crate::leanh::lean_inc(v_k_6140_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6134_, 1);
            v_k_6141_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 0);
            crate::leanh::lean_inc(v_k_6141_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6135_, 1);
            v___x_6142_ = crate::leanh::lean_apply_2(v_h__1_6136_, v_k_6140_, v_k_6141_);
            return v___x_6142_;
        } else {
            let mut v_k_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_6136_);
            v_k_6143_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 0);
            crate::leanh::lean_inc(v_k_6143_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6134_, 1);
            v_k_6144_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 0);
            crate::leanh::lean_inc(v_k_6144_);
            v_v_6145_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 1);
            crate::leanh::lean_inc(v_v_6145_);
            v_p_6146_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 2);
            crate::leanh::lean_inc_ref(v_p_6146_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6135_, 3);
            v___x_6147_ = crate::leanh::lean_apply_4(
                v_h__2_6137_,
                v_k_6143_,
                v_k_6144_,
                v_v_6145_,
                v_p_6146_,
            );
            return v___x_6147_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_6137_);
        crate::leanh::lean_dec(v_h__1_6136_);
        if crate::leanh::lean_obj_tag(v_p_u2082_6135_) == 0 {
            let mut v_k_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_6139_);
            v_k_6148_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 0);
            crate::leanh::lean_inc(v_k_6148_);
            v_v_6149_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 1);
            crate::leanh::lean_inc(v_v_6149_);
            v_p_6150_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 2);
            crate::leanh::lean_inc_ref(v_p_6150_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6134_, 3);
            v_k_6151_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 0);
            crate::leanh::lean_inc(v_k_6151_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6135_, 1);
            v___x_6152_ = crate::leanh::lean_apply_4(
                v_h__3_6138_,
                v_k_6148_,
                v_v_6149_,
                v_p_6150_,
                v_k_6151_,
            );
            return v___x_6152_;
        } else {
            let mut v_k_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6138_);
            v_k_6153_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 0);
            crate::leanh::lean_inc(v_k_6153_);
            v_v_6154_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 1);
            crate::leanh::lean_inc(v_v_6154_);
            v_p_6155_ = crate::leanh::lean_ctor_get(v_p_u2081_6134_, 2);
            crate::leanh::lean_inc_ref(v_p_6155_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6134_, 3);
            v_k_6156_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 0);
            crate::leanh::lean_inc(v_k_6156_);
            v_v_6157_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 1);
            crate::leanh::lean_inc(v_v_6157_);
            v_p_6158_ = crate::leanh::lean_ctor_get(v_p_u2082_6135_, 2);
            crate::leanh::lean_inc_ref(v_p_6158_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6135_, 3);
            v___x_6159_ = crate::leanh::lean_apply_6(
                v_h__4_6139_,
                v_k_6153_,
                v_v_6154_,
                v_p_6155_,
                v_k_6156_,
                v_v_6157_,
                v_p_6158_,
            );
            return v___x_6159_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(
    mut v_motive_6160_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_6161_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6162_: *mut crate::leanh::LeanObject,
    mut v_h__1_6163_: *mut crate::leanh::LeanObject,
    mut v_h__2_6164_: *mut crate::leanh::LeanObject,
    mut v_h__3_6165_: *mut crate::leanh::LeanObject,
    mut v_h__4_6166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_6161_) == 0 {
        crate::leanh::lean_dec(v_h__4_6166_);
        crate::leanh::lean_dec(v_h__3_6165_);
        if crate::leanh::lean_obj_tag(v_p_u2082_6162_) == 0 {
            let mut v_k_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_6164_);
            v_k_6167_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 0);
            crate::leanh::lean_inc(v_k_6167_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6161_, 1);
            v_k_6168_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 0);
            crate::leanh::lean_inc(v_k_6168_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6162_, 1);
            v___x_6169_ = crate::leanh::lean_apply_2(v_h__1_6163_, v_k_6167_, v_k_6168_);
            return v___x_6169_;
        } else {
            let mut v_k_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_6163_);
            v_k_6170_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 0);
            crate::leanh::lean_inc(v_k_6170_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6161_, 1);
            v_k_6171_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 0);
            crate::leanh::lean_inc(v_k_6171_);
            v_v_6172_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 1);
            crate::leanh::lean_inc(v_v_6172_);
            v_p_6173_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 2);
            crate::leanh::lean_inc_ref(v_p_6173_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6162_, 3);
            v___x_6174_ = crate::leanh::lean_apply_4(
                v_h__2_6164_,
                v_k_6170_,
                v_k_6171_,
                v_v_6172_,
                v_p_6173_,
            );
            return v___x_6174_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_6164_);
        crate::leanh::lean_dec(v_h__1_6163_);
        if crate::leanh::lean_obj_tag(v_p_u2082_6162_) == 0 {
            let mut v_k_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_6166_);
            v_k_6175_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 0);
            crate::leanh::lean_inc(v_k_6175_);
            v_v_6176_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 1);
            crate::leanh::lean_inc(v_v_6176_);
            v_p_6177_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 2);
            crate::leanh::lean_inc_ref(v_p_6177_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6161_, 3);
            v_k_6178_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 0);
            crate::leanh::lean_inc(v_k_6178_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6162_, 1);
            v___x_6179_ = crate::leanh::lean_apply_4(
                v_h__3_6165_,
                v_k_6175_,
                v_v_6176_,
                v_p_6177_,
                v_k_6178_,
            );
            return v___x_6179_;
        } else {
            let mut v_k_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6165_);
            v_k_6180_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 0);
            crate::leanh::lean_inc(v_k_6180_);
            v_v_6181_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 1);
            crate::leanh::lean_inc(v_v_6181_);
            v_p_6182_ = crate::leanh::lean_ctor_get(v_p_u2081_6161_, 2);
            crate::leanh::lean_inc_ref(v_p_6182_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_6161_, 3);
            v_k_6183_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 0);
            crate::leanh::lean_inc(v_k_6183_);
            v_v_6184_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 1);
            crate::leanh::lean_inc(v_v_6184_);
            v_p_6185_ = crate::leanh::lean_ctor_get(v_p_u2082_6162_, 2);
            crate::leanh::lean_inc_ref(v_p_6185_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_6162_, 3);
            v___x_6186_ = crate::leanh::lean_apply_6(
                v_h__4_6166_,
                v_k_6180_,
                v_v_6181_,
                v_p_6182_,
                v_k_6183_,
                v_v_6184_,
                v_p_6185_,
            );
            return v___x_6186_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(
    mut v_x_6187_: u8,
    mut v_h__1_6188_: *mut crate::leanh::LeanObject,
    mut v_h__2_6189_: *mut crate::leanh::LeanObject,
    mut v_h__3_6190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_6187_ {
        0 => {
            let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_6189_);
            crate::leanh::lean_dec(v_h__1_6188_);
            v___x_6191_ = crate::leanh::lean_box(0);
            v___x_6192_ = crate::leanh::lean_apply_1(v_h__3_6190_, v___x_6191_);
            return v___x_6192_;
        }
        1 => {
            let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6190_);
            crate::leanh::lean_dec(v_h__2_6189_);
            v___x_6193_ = crate::leanh::lean_box(0);
            v___x_6194_ = crate::leanh::lean_apply_1(v_h__1_6188_, v___x_6193_);
            return v___x_6194_;
        }
        _ => {
            let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6190_);
            crate::leanh::lean_dec(v_h__1_6188_);
            v___x_6195_ = crate::leanh::lean_box(0);
            v___x_6196_ = crate::leanh::lean_apply_1(v_h__2_6189_, v___x_6195_);
            return v___x_6196_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(
    mut v_x_6197_: *mut crate::leanh::LeanObject,
    mut v_h__1_6198_: *mut crate::leanh::LeanObject,
    mut v_h__2_6199_: *mut crate::leanh::LeanObject,
    mut v_h__3_6200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_6201_: u8 = 0;
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_6201_ = (crate::leanh::lean_unbox(v_x_6197_) as u8);
    v_res_6202_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_36__boxed_6201_, v_h__1_6198_, v_h__2_6199_, v_h__3_6200_);
    return v_res_6202_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(
    mut v_motive_6203_: *mut crate::leanh::LeanObject,
    mut v_x_6204_: u8,
    mut v_h__1_6205_: *mut crate::leanh::LeanObject,
    mut v_h__2_6206_: *mut crate::leanh::LeanObject,
    mut v_h__3_6207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_6204_ {
        0 => {
            let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_6206_);
            crate::leanh::lean_dec(v_h__1_6205_);
            v___x_6208_ = crate::leanh::lean_box(0);
            v___x_6209_ = crate::leanh::lean_apply_1(v_h__3_6207_, v___x_6208_);
            return v___x_6209_;
        }
        1 => {
            let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6207_);
            crate::leanh::lean_dec(v_h__2_6206_);
            v___x_6210_ = crate::leanh::lean_box(0);
            v___x_6211_ = crate::leanh::lean_apply_1(v_h__1_6205_, v___x_6210_);
            return v___x_6211_;
        }
        _ => {
            let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6207_);
            crate::leanh::lean_dec(v_h__1_6205_);
            v___x_6212_ = crate::leanh::lean_box(0);
            v___x_6213_ = crate::leanh::lean_apply_1(v_h__2_6206_, v___x_6212_);
            return v___x_6213_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(
    mut v_motive_6214_: *mut crate::leanh::LeanObject,
    mut v_x_6215_: *mut crate::leanh::LeanObject,
    mut v_h__1_6216_: *mut crate::leanh::LeanObject,
    mut v_h__2_6217_: *mut crate::leanh::LeanObject,
    mut v_h__3_6218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_6219_: u8 = 0;
    let mut v_res_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_6219_ = (crate::leanh::lean_unbox(v_x_6215_) as u8);
    v_res_6220_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_6214_, v_x_51__boxed_6219_, v_h__1_6216_, v_h__2_6217_, v_h__3_6218_);
    return v_res_6220_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mul_go(
    mut v_p_u2082_6221_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_6222_: *mut crate::leanh::LeanObject,
    mut v_acc_6223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_6222_) == 0 {
                    v_k_6224_ = crate::leanh::lean_ctor_get(v_p_u2081_6222_, 0);
                    crate::leanh::lean_inc(v_k_6224_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6222_, 1);
                    v___x_6225_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6224_, v_p_u2082_6221_);
                    crate::leanh::lean_dec(v_k_6224_);
                    v___x_6226_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_6223_, v___x_6225_);
                    return v___x_6226_;
                } else {
                    v_k_6227_ = crate::leanh::lean_ctor_get(v_p_u2081_6222_, 0);
                    crate::leanh::lean_inc(v_k_6227_);
                    v_v_6228_ = crate::leanh::lean_ctor_get(v_p_u2081_6222_, 1);
                    crate::leanh::lean_inc(v_v_6228_);
                    v_p_6229_ = crate::leanh::lean_ctor_get(v_p_u2081_6222_, 2);
                    crate::leanh::lean_inc_ref(v_p_6229_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6222_, 3);
                    crate::leanh::lean_inc_ref(v_p_u2082_6221_);
                    v___x_6230_ =
                        l_Lean_Grind_CommRing_Poly_mulMon(v_k_6227_, v_v_6228_, v_p_u2082_6221_);
                    crate::leanh::lean_dec(v_k_6227_);
                    v___x_6231_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_6223_, v___x_6230_);
                    v_p_u2081_6222_ = v_p_6229_;
                    v_acc_6223_ = v___x_6231_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mul(
    mut v_p_u2081_6233_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6236_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_6234_, v_p_u2081_6233_, v___x_6235_);
    return v___x_6236_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mul__nc_go(
    mut v_p_u2082_6237_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_6238_: *mut crate::leanh::LeanObject,
    mut v_acc_6239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_6238_) == 0 {
                    v_k_6240_ = crate::leanh::lean_ctor_get(v_p_u2081_6238_, 0);
                    crate::leanh::lean_inc(v_k_6240_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6238_, 1);
                    v___x_6241_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6240_, v_p_u2082_6237_);
                    crate::leanh::lean_dec(v_k_6240_);
                    v___x_6242_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_6239_, v___x_6241_);
                    return v___x_6242_;
                } else {
                    v_k_6243_ = crate::leanh::lean_ctor_get(v_p_u2081_6238_, 0);
                    crate::leanh::lean_inc(v_k_6243_);
                    v_v_6244_ = crate::leanh::lean_ctor_get(v_p_u2081_6238_, 1);
                    crate::leanh::lean_inc(v_v_6244_);
                    v_p_6245_ = crate::leanh::lean_ctor_get(v_p_u2081_6238_, 2);
                    crate::leanh::lean_inc_ref(v_p_6245_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6238_, 3);
                    crate::leanh::lean_inc_ref(v_p_u2082_6237_);
                    v___x_6246_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(
                        v_k_6243_,
                        v_v_6244_,
                        v_p_u2082_6237_,
                    );
                    crate::leanh::lean_dec(v_k_6243_);
                    v___x_6247_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_6239_, v___x_6246_);
                    v_p_u2081_6238_ = v_p_6245_;
                    v_acc_6239_ = v___x_6247_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mul__nc(
    mut v_p_u2081_6249_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6252_ =
        l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_6250_, v_p_u2081_6249_, v___x_6251_);
    return v___x_6252_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_pow___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6253_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_6254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6254_, 0, v___x_6253_);
    return v___x_6254_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow(
    mut v_p_6255_: *mut crate::leanh::LeanObject,
    mut v_k_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6258_: u8 = 0;
    v_zero_6257_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6258_ = lean_nat_dec_eq(v_k_6256_, v_zero_6257_);
    if v_isZero_6258_ == 1 {
        let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_6255_);
        v___x_6259_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6259_;
    } else {
        let mut v_one_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6262_: u8 = 0;
        v_one_6260_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6261_ = lean_nat_sub(v_k_6256_, v_one_6260_);
        v___x_6262_ = lean_nat_dec_eq(v_n_6261_, v_zero_6257_);
        if v___x_6262_ == 0 {
            let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_p_6255_);
            v___x_6263_ = l_Lean_Grind_CommRing_Poly_pow(v_p_6255_, v_n_6261_);
            crate::leanh::lean_dec(v_n_6261_);
            v___x_6264_ = l_Lean_Grind_CommRing_Poly_mul(v_p_6255_, v___x_6263_);
            return v___x_6264_;
        } else {
            crate::leanh::lean_dec(v_n_6261_);
            return v_p_6255_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow___boxed(
    mut v_p_6265_: *mut crate::leanh::LeanObject,
    mut v_k_6266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6267_ = l_Lean_Grind_CommRing_Poly_pow(v_p_6265_, v_k_6266_);
    crate::leanh::lean_dec(v_k_6266_);
    return v_res_6267_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow__nc(
    mut v_p_6268_: *mut crate::leanh::LeanObject,
    mut v_k_6269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6271_: u8 = 0;
    v_zero_6270_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6271_ = lean_nat_dec_eq(v_k_6269_, v_zero_6270_);
    if v_isZero_6271_ == 1 {
        let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_6268_);
        v___x_6272_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6272_;
    } else {
        let mut v_one_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6275_: u8 = 0;
        v_one_6273_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6274_ = lean_nat_sub(v_k_6269_, v_one_6273_);
        v___x_6275_ = lean_nat_dec_eq(v_n_6274_, v_zero_6270_);
        if v___x_6275_ == 0 {
            let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_p_6268_);
            v___x_6276_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_6268_, v_n_6274_);
            crate::leanh::lean_dec(v_n_6274_);
            v___x_6277_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_6276_, v_p_6268_);
            return v___x_6277_;
        } else {
            crate::leanh::lean_dec(v_n_6274_);
            return v_p_6268_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow__nc___boxed(
    mut v_p_6278_: *mut crate::leanh::LeanObject,
    mut v_k_6279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6280_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_6278_, v_k_6279_);
    crate::leanh::lean_dec(v_k_6279_);
    return v_res_6280_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6281_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_6282_ = lean_int_neg(v___x_6281_);
    return v___x_6282_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPoly(
    mut v_x_6283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6291_: u8 = 0;
    let mut v_k_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut v_k_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6304_: u8 = 0;
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6308_: u8 = 0;
    let mut v_i_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v_n_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: u8 = 0;
    let mut v_k_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6348_: u8 = 0;
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6354_: u8 = 0;
    let mut v_i_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_6283_) {
                0 => {
                    v_k_6284_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    v_isSharedCheck_6291_ = (!crate::leanh::lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6291_ == 0 {
                        v___x_6286_ = v_x_6283_;
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6284_);
                        crate::leanh::lean_dec(v_x_6283_);
                        v___x_6286_ = crate::leanh::lean_box(0);
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_6292_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    v_isSharedCheck_6300_ = (!crate::leanh::lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6300_ == 0 {
                        v___x_6294_ = v_x_6283_;
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6292_);
                        crate::leanh::lean_dec(v_x_6283_);
                        v___x_6294_ = crate::leanh::lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_k_6301_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    v_isSharedCheck_6308_ = (!crate::leanh::lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6308_ == 0 {
                        v___x_6303_ = v_x_6283_;
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6301_);
                        crate::leanh::lean_dec(v_x_6283_);
                        v___x_6303_ = crate::leanh::lean_box(0);
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_6309_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    crate::leanh::lean_inc(v_i_6309_);
                    crate::leanh::lean_dec_ref_known(v_x_6283_, 1);
                    v___x_6310_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_6309_);
                    return v___x_6310_;
                }
                4 => {
                    v_a_6311_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    crate::leanh::lean_inc_ref(v_a_6311_);
                    crate::leanh::lean_dec_ref_known(v_x_6283_, 1);
                    v___x_6312_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_6313_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6311_);
                    v___x_6314_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_6312_, v___x_6313_);
                    return v___x_6314_;
                }
                5 => {
                    v_a_6315_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    crate::leanh::lean_inc_ref(v_a_6315_);
                    v_b_6316_ = crate::leanh::lean_ctor_get(v_x_6283_, 1);
                    crate::leanh::lean_inc_ref(v_b_6316_);
                    crate::leanh::lean_dec_ref_known(v_x_6283_, 2);
                    v___x_6317_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6315_);
                    v___x_6318_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_6316_);
                    v___x_6319_ = l_Lean_Grind_CommRing_Poly_combine(v___x_6317_, v___x_6318_);
                    return v___x_6319_;
                }
                6 => {
                    v_a_6320_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    crate::leanh::lean_inc_ref(v_a_6320_);
                    v_b_6321_ = crate::leanh::lean_ctor_get(v_x_6283_, 1);
                    crate::leanh::lean_inc_ref(v_b_6321_);
                    crate::leanh::lean_dec_ref_known(v_x_6283_, 2);
                    v___x_6322_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6320_);
                    v___x_6323_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_6324_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_6321_);
                    v___x_6325_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_6323_, v___x_6324_);
                    v___x_6326_ = l_Lean_Grind_CommRing_Poly_combine(v___x_6322_, v___x_6325_);
                    return v___x_6326_;
                }
                7 => {
                    v_a_6327_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    crate::leanh::lean_inc_ref(v_a_6327_);
                    v_b_6328_ = crate::leanh::lean_ctor_get(v_x_6283_, 1);
                    crate::leanh::lean_inc_ref(v_b_6328_);
                    crate::leanh::lean_dec_ref_known(v_x_6283_, 2);
                    v___x_6329_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6327_);
                    v___x_6330_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_6328_);
                    v___x_6331_ = l_Lean_Grind_CommRing_Poly_mul(v___x_6329_, v___x_6330_);
                    return v___x_6331_;
                }
                _ => {
                    v_a_6332_ = crate::leanh::lean_ctor_get(v_x_6283_, 0);
                    v_k_6333_ = crate::leanh::lean_ctor_get(v_x_6283_, 1);
                    v_isSharedCheck_6365_ = (!crate::leanh::lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6365_ == 0 {
                        v___x_6335_ = v_x_6283_;
                        v_isShared_6336_ = v_isSharedCheck_6365_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6333_);
                        crate::leanh::lean_inc(v_a_6332_);
                        crate::leanh::lean_dec(v_x_6283_);
                        v___x_6335_ = crate::leanh::lean_box(0);
                        v_isShared_6336_ = v_isSharedCheck_6365_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_6287_ == 0 {
                    v___x_6289_ = v___x_6286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_k_6284_);
                    v___x_6289_ = v_reuseFailAlloc_6290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6289_;
            }
            3 => {
                v___x_6296_ = lean_nat_to_int(v_k_6292_);
                if v_isShared_6295_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6294_, 0);
                    crate::leanh::lean_ctor_set(v___x_6294_, 0, v___x_6296_);
                    v___x_6298_ = v___x_6294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6299_, 0, v___x_6296_);
                    v___x_6298_ = v_reuseFailAlloc_6299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6298_;
            }
            5 => {
                if v_isShared_6304_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6303_, 0);
                    v___x_6306_ = v___x_6303_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6307_, 0, v_k_6301_);
                    v___x_6306_ = v_reuseFailAlloc_6307_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6306_;
            }
            7 => {
                v___x_6341_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6342_ = lean_nat_dec_eq(v_k_6333_, v___x_6341_);
                if v___x_6342_ == 0 {
                    match crate::leanh::lean_obj_tag(v_a_6332_) {
                        0 => {
                            crate::leanh::lean_del_object(v___x_6335_);
                            v_k_6343_ = crate::leanh::lean_ctor_get(v_a_6332_, 0);
                            crate::leanh::lean_inc(v_k_6343_);
                            crate::leanh::lean_dec_ref_known(v_a_6332_, 1);
                            v_n_6338_ = v_k_6343_;
                            state = 8;
                            continue;
                        }
                        2 => {
                            crate::leanh::lean_del_object(v___x_6335_);
                            v_k_6344_ = crate::leanh::lean_ctor_get(v_a_6332_, 0);
                            crate::leanh::lean_inc(v_k_6344_);
                            crate::leanh::lean_dec_ref_known(v_a_6332_, 1);
                            v_n_6338_ = v_k_6344_;
                            state = 8;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_del_object(v___x_6335_);
                            v_k_6345_ = crate::leanh::lean_ctor_get(v_a_6332_, 0);
                            v_isSharedCheck_6354_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6332_)) as u8;
                            if v_isSharedCheck_6354_ == 0 {
                                v___x_6347_ = v_a_6332_;
                                v_isShared_6348_ = v_isSharedCheck_6354_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_6345_);
                                crate::leanh::lean_dec(v_a_6332_);
                                v___x_6347_ = crate::leanh::lean_box(0);
                                v_isShared_6348_ = v_isSharedCheck_6354_;
                                state = 9;
                                continue;
                            }
                        }
                        3 => {
                            v_i_6355_ = crate::leanh::lean_ctor_get(v_a_6332_, 0);
                            crate::leanh::lean_inc(v_i_6355_);
                            crate::leanh::lean_dec_ref_known(v_a_6332_, 1);
                            if v_isShared_6336_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6335_, 0);
                                crate::leanh::lean_ctor_set(v___x_6335_, 0, v_i_6355_);
                                v___x_6357_ = v___x_6335_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_6361_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_i_6355_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 1, v_k_6333_);
                                v___x_6357_ = v_reuseFailAlloc_6361_;
                                state = 11;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_del_object(v___x_6335_);
                            v___x_6362_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6332_);
                            v___x_6363_ = l_Lean_Grind_CommRing_Poly_pow(v___x_6362_, v_k_6333_);
                            crate::leanh::lean_dec(v_k_6333_);
                            return v___x_6363_;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6335_);
                    crate::leanh::lean_dec(v_k_6333_);
                    crate::leanh::lean_dec_ref(v_a_6332_);
                    v___x_6364_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_6364_;
                }
            }
            8 => {
                v___x_6339_ = l_Int_pow(v_n_6338_, v_k_6333_);
                crate::leanh::lean_dec(v_k_6333_);
                crate::leanh::lean_dec(v_n_6338_);
                v___x_6340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6340_, 0, v___x_6339_);
                return v___x_6340_;
            }
            9 => {
                v___x_6349_ = lean_nat_to_int(v_k_6345_);
                v___x_6350_ = l_Int_pow(v___x_6349_, v_k_6333_);
                crate::leanh::lean_dec(v_k_6333_);
                crate::leanh::lean_dec(v___x_6349_);
                if v_isShared_6348_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6347_, 0);
                    crate::leanh::lean_ctor_set(v___x_6347_, 0, v___x_6350_);
                    v___x_6352_ = v___x_6347_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6350_);
                    v___x_6352_ = v_reuseFailAlloc_6353_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6352_;
            }
            11 => {
                v___x_6358_ = crate::leanh::lean_box(0);
                v___x_6359_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6359_, 0, v___x_6357_);
                crate::leanh::lean_ctor_set(v___x_6359_, 1, v___x_6358_);
                v___x_6360_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_6359_);
                return v___x_6360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degreeOf(
    mut v_m_6366_: *mut crate::leanh::LeanObject,
    mut v_x_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_6366_) == 0 {
                    v___x_6368_ = crate::leanh::lean_unsigned_to_nat(0);
                    return v___x_6368_;
                } else {
                    v_p_6369_ = crate::leanh::lean_ctor_get(v_m_6366_, 0);
                    v_m_6370_ = crate::leanh::lean_ctor_get(v_m_6366_, 1);
                    v_x_6371_ = crate::leanh::lean_ctor_get(v_p_6369_, 0);
                    v_k_6372_ = crate::leanh::lean_ctor_get(v_p_6369_, 1);
                    v___x_6373_ = lean_nat_dec_eq(v_x_6371_, v_x_6367_);
                    if v___x_6373_ == 0 {
                        v_m_6366_ = v_m_6370_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6372_);
                        return v_k_6372_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degreeOf___boxed(
    mut v_m_6375_: *mut crate::leanh::LeanObject,
    mut v_x_6376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6377_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_6375_, v_x_6376_);
    crate::leanh::lean_dec(v_x_6376_);
    crate::leanh::lean_dec(v_m_6375_);
    return v_res_6377_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_cancelVar(
    mut v_m_6378_: *mut crate::leanh::LeanObject,
    mut v_x_6379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6384_: u8 = 0;
    let mut v_x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: u8 = 0;
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_6378_) == 0 {
                    return v_m_6378_;
                } else {
                    v_p_6380_ = crate::leanh::lean_ctor_get(v_m_6378_, 0);
                    v_m_6381_ = crate::leanh::lean_ctor_get(v_m_6378_, 1);
                    v_isSharedCheck_6391_ = (!crate::leanh::lean_is_exclusive(v_m_6378_)) as u8;
                    if v_isSharedCheck_6391_ == 0 {
                        v___x_6383_ = v_m_6378_;
                        v_isShared_6384_ = v_isSharedCheck_6391_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_m_6381_);
                        crate::leanh::lean_inc(v_p_6380_);
                        crate::leanh::lean_dec(v_m_6378_);
                        v___x_6383_ = crate::leanh::lean_box(0);
                        v_isShared_6384_ = v_isSharedCheck_6391_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_x_6385_ = crate::leanh::lean_ctor_get(v_p_6380_, 0);
                v___x_6386_ = lean_nat_dec_eq(v_x_6385_, v_x_6379_);
                if v___x_6386_ == 0 {
                    v___x_6387_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_6381_, v_x_6379_);
                    if v_isShared_6384_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6383_, 1, v___x_6387_);
                        v___x_6389_ = v___x_6383_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6390_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_p_6380_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6390_, 1, v___x_6387_);
                        v___x_6389_ = v_reuseFailAlloc_6390_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6383_);
                    crate::leanh::lean_dec_ref(v_p_6380_);
                    return v_m_6381_;
                }
            }
            2 => {
                return v___x_6389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_cancelVar___boxed(
    mut v_m_6392_: *mut crate::leanh::LeanObject,
    mut v_x_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_6392_, v_x_6393_);
    crate::leanh::lean_dec(v_x_6393_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar_x27(
    mut v_c_6395_: *mut crate::leanh::LeanObject,
    mut v_x_6396_: *mut crate::leanh::LeanObject,
    mut v_p_6397_: *mut crate::leanh::LeanObject,
    mut v_acc_6398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6406_: u8 = 0;
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: u8 = 0;
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_6397_) == 0 {
                    v_k_6399_ = crate::leanh::lean_ctor_get(v_p_6397_, 0);
                    crate::leanh::lean_inc(v_k_6399_);
                    crate::leanh::lean_dec_ref_known(v_p_6397_, 1);
                    v___x_6400_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_6398_, v_k_6399_);
                    crate::leanh::lean_dec(v_k_6399_);
                    return v___x_6400_;
                } else {
                    v_k_6401_ = crate::leanh::lean_ctor_get(v_p_6397_, 0);
                    crate::leanh::lean_inc(v_k_6401_);
                    v_v_6402_ = crate::leanh::lean_ctor_get(v_p_6397_, 1);
                    crate::leanh::lean_inc(v_v_6402_);
                    v_p_6403_ = crate::leanh::lean_ctor_get(v_p_6397_, 2);
                    crate::leanh::lean_inc_ref(v_p_6403_);
                    crate::leanh::lean_dec_ref_known(v_p_6397_, 3);
                    v_n_6404_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_6402_, v_x_6396_);
                    v___x_6414_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6415_ = lean_nat_dec_lt(v___x_6414_, v_n_6404_);
                    if v___x_6415_ == 0 {
                        v___y_6406_ = v___x_6415_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6416_ = l_Int_pow(v_c_6395_, v_n_6404_);
                        v___x_6417_ = l_Int_decidableDvd(v___x_6416_, v_k_6401_);
                        crate::leanh::lean_dec(v___x_6416_);
                        v___y_6406_ = v___x_6417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6406_ == 0 {
                    crate::leanh::lean_dec(v_n_6404_);
                    v___x_6407_ =
                        l_Lean_Grind_CommRing_Poly_insert(v_k_6401_, v_v_6402_, v_acc_6398_);
                    v_p_6397_ = v_p_6403_;
                    v_acc_6398_ = v___x_6407_;
                    state = 0;
                    continue;
                } else {
                    v___x_6409_ = l_Int_pow(v_c_6395_, v_n_6404_);
                    crate::leanh::lean_dec(v_n_6404_);
                    v___x_6410_ = lean_int_ediv(v_k_6401_, v___x_6409_);
                    crate::leanh::lean_dec(v___x_6409_);
                    crate::leanh::lean_dec(v_k_6401_);
                    v___x_6411_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_6402_, v_x_6396_);
                    v___x_6412_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6410_, v___x_6411_, v_acc_6398_);
                    v_p_6397_ = v_p_6403_;
                    v_acc_6398_ = v___x_6412_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(
    mut v_c_6418_: *mut crate::leanh::LeanObject,
    mut v_x_6419_: *mut crate::leanh::LeanObject,
    mut v_p_6420_: *mut crate::leanh::LeanObject,
    mut v_acc_6421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6422_ =
        l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_6418_, v_x_6419_, v_p_6420_, v_acc_6421_);
    crate::leanh::lean_dec(v_x_6419_);
    crate::leanh::lean_dec(v_c_6418_);
    return v_res_6422_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar(
    mut v_c_6423_: *mut crate::leanh::LeanObject,
    mut v_x_6424_: *mut crate::leanh::LeanObject,
    mut v_p_6425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6427_ =
        l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_6423_, v_x_6424_, v_p_6425_, v___x_6426_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar___boxed(
    mut v_c_6428_: *mut crate::leanh::LeanObject,
    mut v_x_6429_: *mut crate::leanh::LeanObject,
    mut v_p_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6431_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_6428_, v_x_6429_, v_p_6430_);
    crate::leanh::lean_dec(v_x_6429_);
    crate::leanh::lean_dec(v_c_6428_);
    return v_res_6431_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(
    mut v_x_6432_: *mut crate::leanh::LeanObject,
    mut v_h__1_6433_: *mut crate::leanh::LeanObject,
    mut v_h__2_6434_: *mut crate::leanh::LeanObject,
    mut v_h__3_6435_: *mut crate::leanh::LeanObject,
    mut v_h__4_6436_: *mut crate::leanh::LeanObject,
    mut v_h__5_6437_: *mut crate::leanh::LeanObject,
    mut v_h__6_6438_: *mut crate::leanh::LeanObject,
    mut v_h__7_6439_: *mut crate::leanh::LeanObject,
    mut v_h__8_6440_: *mut crate::leanh::LeanObject,
    mut v_h__9_6441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_6432_) {
        0 => {
            let mut v_k_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            v_k_6442_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc(v_k_6442_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 1);
            v___x_6443_ = crate::leanh::lean_apply_1(v_h__1_6433_, v_k_6442_);
            return v___x_6443_;
        }
        1 => {
            let mut v_k_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_k_6444_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc(v_k_6444_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 1);
            v___x_6445_ = crate::leanh::lean_apply_1(v_h__3_6435_, v_k_6444_);
            return v___x_6445_;
        }
        2 => {
            let mut v_k_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_k_6446_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc(v_k_6446_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 1);
            v___x_6447_ = crate::leanh::lean_apply_1(v_h__2_6434_, v_k_6446_);
            return v___x_6447_;
        }
        3 => {
            let mut v_i_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_i_6448_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc(v_i_6448_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 1);
            v___x_6449_ = crate::leanh::lean_apply_1(v_h__4_6436_, v_i_6448_);
            return v___x_6449_;
        }
        4 => {
            let mut v_a_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_a_6450_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc_ref(v_a_6450_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 1);
            v___x_6451_ = crate::leanh::lean_apply_1(v_h__7_6439_, v_a_6450_);
            return v___x_6451_;
        }
        5 => {
            let mut v_a_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_a_6452_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc_ref(v_a_6452_);
            v_b_6453_ = crate::leanh::lean_ctor_get(v_x_6432_, 1);
            crate::leanh::lean_inc_ref(v_b_6453_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 2);
            v___x_6454_ = crate::leanh::lean_apply_2(v_h__5_6437_, v_a_6452_, v_b_6453_);
            return v___x_6454_;
        }
        6 => {
            let mut v_a_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_a_6455_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc_ref(v_a_6455_);
            v_b_6456_ = crate::leanh::lean_ctor_get(v_x_6432_, 1);
            crate::leanh::lean_inc_ref(v_b_6456_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 2);
            v___x_6457_ = crate::leanh::lean_apply_2(v_h__8_6440_, v_a_6455_, v_b_6456_);
            return v___x_6457_;
        }
        7 => {
            let mut v_a_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6441_);
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_a_6458_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc_ref(v_a_6458_);
            v_b_6459_ = crate::leanh::lean_ctor_get(v_x_6432_, 1);
            crate::leanh::lean_inc_ref(v_b_6459_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 2);
            v___x_6460_ = crate::leanh::lean_apply_2(v_h__6_6438_, v_a_6458_, v_b_6459_);
            return v___x_6460_;
        }
        _ => {
            let mut v_a_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_6440_);
            crate::leanh::lean_dec(v_h__7_6439_);
            crate::leanh::lean_dec(v_h__6_6438_);
            crate::leanh::lean_dec(v_h__5_6437_);
            crate::leanh::lean_dec(v_h__4_6436_);
            crate::leanh::lean_dec(v_h__3_6435_);
            crate::leanh::lean_dec(v_h__2_6434_);
            crate::leanh::lean_dec(v_h__1_6433_);
            v_a_6461_ = crate::leanh::lean_ctor_get(v_x_6432_, 0);
            crate::leanh::lean_inc_ref(v_a_6461_);
            v_k_6462_ = crate::leanh::lean_ctor_get(v_x_6432_, 1);
            crate::leanh::lean_inc(v_k_6462_);
            crate::leanh::lean_dec_ref_known(v_x_6432_, 2);
            v___x_6463_ = crate::leanh::lean_apply_2(v_h__9_6441_, v_a_6461_, v_k_6462_);
            return v___x_6463_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(
    mut v_motive_6464_: *mut crate::leanh::LeanObject,
    mut v_x_6465_: *mut crate::leanh::LeanObject,
    mut v_h__1_6466_: *mut crate::leanh::LeanObject,
    mut v_h__2_6467_: *mut crate::leanh::LeanObject,
    mut v_h__3_6468_: *mut crate::leanh::LeanObject,
    mut v_h__4_6469_: *mut crate::leanh::LeanObject,
    mut v_h__5_6470_: *mut crate::leanh::LeanObject,
    mut v_h__6_6471_: *mut crate::leanh::LeanObject,
    mut v_h__7_6472_: *mut crate::leanh::LeanObject,
    mut v_h__8_6473_: *mut crate::leanh::LeanObject,
    mut v_h__9_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_6465_) {
        0 => {
            let mut v_k_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            v_k_6475_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc(v_k_6475_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 1);
            v___x_6476_ = crate::leanh::lean_apply_1(v_h__1_6466_, v_k_6475_);
            return v___x_6476_;
        }
        1 => {
            let mut v_k_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_k_6477_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc(v_k_6477_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 1);
            v___x_6478_ = crate::leanh::lean_apply_1(v_h__3_6468_, v_k_6477_);
            return v___x_6478_;
        }
        2 => {
            let mut v_k_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_k_6479_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc(v_k_6479_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 1);
            v___x_6480_ = crate::leanh::lean_apply_1(v_h__2_6467_, v_k_6479_);
            return v___x_6480_;
        }
        3 => {
            let mut v_i_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_i_6481_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc(v_i_6481_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 1);
            v___x_6482_ = crate::leanh::lean_apply_1(v_h__4_6469_, v_i_6481_);
            return v___x_6482_;
        }
        4 => {
            let mut v_a_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_a_6483_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc_ref(v_a_6483_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 1);
            v___x_6484_ = crate::leanh::lean_apply_1(v_h__7_6472_, v_a_6483_);
            return v___x_6484_;
        }
        5 => {
            let mut v_a_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_a_6485_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc_ref(v_a_6485_);
            v_b_6486_ = crate::leanh::lean_ctor_get(v_x_6465_, 1);
            crate::leanh::lean_inc_ref(v_b_6486_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 2);
            v___x_6487_ = crate::leanh::lean_apply_2(v_h__5_6470_, v_a_6485_, v_b_6486_);
            return v___x_6487_;
        }
        6 => {
            let mut v_a_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_a_6488_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc_ref(v_a_6488_);
            v_b_6489_ = crate::leanh::lean_ctor_get(v_x_6465_, 1);
            crate::leanh::lean_inc_ref(v_b_6489_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 2);
            v___x_6490_ = crate::leanh::lean_apply_2(v_h__8_6473_, v_a_6488_, v_b_6489_);
            return v___x_6490_;
        }
        7 => {
            let mut v_a_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_6474_);
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_a_6491_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc_ref(v_a_6491_);
            v_b_6492_ = crate::leanh::lean_ctor_get(v_x_6465_, 1);
            crate::leanh::lean_inc_ref(v_b_6492_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 2);
            v___x_6493_ = crate::leanh::lean_apply_2(v_h__6_6471_, v_a_6491_, v_b_6492_);
            return v___x_6493_;
        }
        _ => {
            let mut v_a_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_6473_);
            crate::leanh::lean_dec(v_h__7_6472_);
            crate::leanh::lean_dec(v_h__6_6471_);
            crate::leanh::lean_dec(v_h__5_6470_);
            crate::leanh::lean_dec(v_h__4_6469_);
            crate::leanh::lean_dec(v_h__3_6468_);
            crate::leanh::lean_dec(v_h__2_6467_);
            crate::leanh::lean_dec(v_h__1_6466_);
            v_a_6494_ = crate::leanh::lean_ctor_get(v_x_6465_, 0);
            crate::leanh::lean_inc_ref(v_a_6494_);
            v_k_6495_ = crate::leanh::lean_ctor_get(v_x_6465_, 1);
            crate::leanh::lean_inc(v_k_6495_);
            crate::leanh::lean_dec_ref_known(v_x_6465_, 2);
            v___x_6496_ = crate::leanh::lean_apply_2(v_h__9_6474_, v_a_6494_, v_k_6495_);
            return v___x_6496_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(
    mut v_a_6497_: *mut crate::leanh::LeanObject,
    mut v_h__1_6498_: *mut crate::leanh::LeanObject,
    mut v_h__2_6499_: *mut crate::leanh::LeanObject,
    mut v_h__3_6500_: *mut crate::leanh::LeanObject,
    mut v_h__4_6501_: *mut crate::leanh::LeanObject,
    mut v_h__5_6502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_6497_) {
        0 => {
            let mut v_k_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6502_);
            crate::leanh::lean_dec(v_h__4_6501_);
            crate::leanh::lean_dec(v_h__3_6500_);
            crate::leanh::lean_dec(v_h__2_6499_);
            v_k_6503_ = crate::leanh::lean_ctor_get(v_a_6497_, 0);
            crate::leanh::lean_inc(v_k_6503_);
            crate::leanh::lean_dec_ref_known(v_a_6497_, 1);
            v___x_6504_ = crate::leanh::lean_apply_1(v_h__1_6498_, v_k_6503_);
            return v___x_6504_;
        }
        2 => {
            let mut v_k_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6502_);
            crate::leanh::lean_dec(v_h__4_6501_);
            crate::leanh::lean_dec(v_h__3_6500_);
            crate::leanh::lean_dec(v_h__1_6498_);
            v_k_6505_ = crate::leanh::lean_ctor_get(v_a_6497_, 0);
            crate::leanh::lean_inc(v_k_6505_);
            crate::leanh::lean_dec_ref_known(v_a_6497_, 1);
            v___x_6506_ = crate::leanh::lean_apply_1(v_h__2_6499_, v_k_6505_);
            return v___x_6506_;
        }
        1 => {
            let mut v_k_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6502_);
            crate::leanh::lean_dec(v_h__4_6501_);
            crate::leanh::lean_dec(v_h__2_6499_);
            crate::leanh::lean_dec(v_h__1_6498_);
            v_k_6507_ = crate::leanh::lean_ctor_get(v_a_6497_, 0);
            crate::leanh::lean_inc(v_k_6507_);
            crate::leanh::lean_dec_ref_known(v_a_6497_, 1);
            v___x_6508_ = crate::leanh::lean_apply_1(v_h__3_6500_, v_k_6507_);
            return v___x_6508_;
        }
        3 => {
            let mut v_i_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6502_);
            crate::leanh::lean_dec(v_h__3_6500_);
            crate::leanh::lean_dec(v_h__2_6499_);
            crate::leanh::lean_dec(v_h__1_6498_);
            v_i_6509_ = crate::leanh::lean_ctor_get(v_a_6497_, 0);
            crate::leanh::lean_inc(v_i_6509_);
            crate::leanh::lean_dec_ref_known(v_a_6497_, 1);
            v___x_6510_ = crate::leanh::lean_apply_1(v_h__4_6501_, v_i_6509_);
            return v___x_6510_;
        }
        _ => {
            let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_6501_);
            crate::leanh::lean_dec(v_h__3_6500_);
            crate::leanh::lean_dec(v_h__2_6499_);
            crate::leanh::lean_dec(v_h__1_6498_);
            v___x_6511_ = crate::leanh::lean_apply_5(
                v_h__5_6502_,
                v_a_6497_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_6511_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(
    mut v_motive_6512_: *mut crate::leanh::LeanObject,
    mut v_a_6513_: *mut crate::leanh::LeanObject,
    mut v_h__1_6514_: *mut crate::leanh::LeanObject,
    mut v_h__2_6515_: *mut crate::leanh::LeanObject,
    mut v_h__3_6516_: *mut crate::leanh::LeanObject,
    mut v_h__4_6517_: *mut crate::leanh::LeanObject,
    mut v_h__5_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_6513_) {
        0 => {
            let mut v_k_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6518_);
            crate::leanh::lean_dec(v_h__4_6517_);
            crate::leanh::lean_dec(v_h__3_6516_);
            crate::leanh::lean_dec(v_h__2_6515_);
            v_k_6519_ = crate::leanh::lean_ctor_get(v_a_6513_, 0);
            crate::leanh::lean_inc(v_k_6519_);
            crate::leanh::lean_dec_ref_known(v_a_6513_, 1);
            v___x_6520_ = crate::leanh::lean_apply_1(v_h__1_6514_, v_k_6519_);
            return v___x_6520_;
        }
        2 => {
            let mut v_k_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6518_);
            crate::leanh::lean_dec(v_h__4_6517_);
            crate::leanh::lean_dec(v_h__3_6516_);
            crate::leanh::lean_dec(v_h__1_6514_);
            v_k_6521_ = crate::leanh::lean_ctor_get(v_a_6513_, 0);
            crate::leanh::lean_inc(v_k_6521_);
            crate::leanh::lean_dec_ref_known(v_a_6513_, 1);
            v___x_6522_ = crate::leanh::lean_apply_1(v_h__2_6515_, v_k_6521_);
            return v___x_6522_;
        }
        1 => {
            let mut v_k_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6518_);
            crate::leanh::lean_dec(v_h__4_6517_);
            crate::leanh::lean_dec(v_h__2_6515_);
            crate::leanh::lean_dec(v_h__1_6514_);
            v_k_6523_ = crate::leanh::lean_ctor_get(v_a_6513_, 0);
            crate::leanh::lean_inc(v_k_6523_);
            crate::leanh::lean_dec_ref_known(v_a_6513_, 1);
            v___x_6524_ = crate::leanh::lean_apply_1(v_h__3_6516_, v_k_6523_);
            return v___x_6524_;
        }
        3 => {
            let mut v_i_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_6518_);
            crate::leanh::lean_dec(v_h__3_6516_);
            crate::leanh::lean_dec(v_h__2_6515_);
            crate::leanh::lean_dec(v_h__1_6514_);
            v_i_6525_ = crate::leanh::lean_ctor_get(v_a_6513_, 0);
            crate::leanh::lean_inc(v_i_6525_);
            crate::leanh::lean_dec_ref_known(v_a_6513_, 1);
            v___x_6526_ = crate::leanh::lean_apply_1(v_h__4_6517_, v_i_6525_);
            return v___x_6526_;
        }
        _ => {
            let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_6517_);
            crate::leanh::lean_dec(v_h__3_6516_);
            crate::leanh::lean_dec(v_h__2_6515_);
            crate::leanh::lean_dec(v_h__1_6514_);
            v___x_6527_ = crate::leanh::lean_apply_5(
                v_h__5_6518_,
                v_a_6513_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_6527_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPoly__nc(
    mut v_x_6528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut v_k_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6540_: u8 = 0;
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6545_: u8 = 0;
    let mut v_k_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6549_: u8 = 0;
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6553_: u8 = 0;
    let mut v_i_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6581_: u8 = 0;
    let mut v_n_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: u8 = 0;
    let mut v_k_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6593_: u8 = 0;
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_i_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_6528_) {
                0 => {
                    v_k_6529_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    v_isSharedCheck_6536_ = (!crate::leanh::lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6536_ == 0 {
                        v___x_6531_ = v_x_6528_;
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6529_);
                        crate::leanh::lean_dec(v_x_6528_);
                        v___x_6531_ = crate::leanh::lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_6537_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    v_isSharedCheck_6545_ = (!crate::leanh::lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6545_ == 0 {
                        v___x_6539_ = v_x_6528_;
                        v_isShared_6540_ = v_isSharedCheck_6545_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6537_);
                        crate::leanh::lean_dec(v_x_6528_);
                        v___x_6539_ = crate::leanh::lean_box(0);
                        v_isShared_6540_ = v_isSharedCheck_6545_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_k_6546_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    v_isSharedCheck_6553_ = (!crate::leanh::lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6553_ == 0 {
                        v___x_6548_ = v_x_6528_;
                        v_isShared_6549_ = v_isSharedCheck_6553_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6546_);
                        crate::leanh::lean_dec(v_x_6528_);
                        v___x_6548_ = crate::leanh::lean_box(0);
                        v_isShared_6549_ = v_isSharedCheck_6553_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_6554_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    crate::leanh::lean_inc(v_i_6554_);
                    crate::leanh::lean_dec_ref_known(v_x_6528_, 1);
                    v___x_6555_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_6554_);
                    return v___x_6555_;
                }
                4 => {
                    v_a_6556_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    crate::leanh::lean_inc_ref(v_a_6556_);
                    crate::leanh::lean_dec_ref_known(v_x_6528_, 1);
                    v___x_6557_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_6558_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6556_);
                    v___x_6559_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_6557_, v___x_6558_);
                    return v___x_6559_;
                }
                5 => {
                    v_a_6560_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    crate::leanh::lean_inc_ref(v_a_6560_);
                    v_b_6561_ = crate::leanh::lean_ctor_get(v_x_6528_, 1);
                    crate::leanh::lean_inc_ref(v_b_6561_);
                    crate::leanh::lean_dec_ref_known(v_x_6528_, 2);
                    v___x_6562_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6560_);
                    v___x_6563_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_6561_);
                    v___x_6564_ = l_Lean_Grind_CommRing_Poly_combine(v___x_6562_, v___x_6563_);
                    return v___x_6564_;
                }
                6 => {
                    v_a_6565_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    crate::leanh::lean_inc_ref(v_a_6565_);
                    v_b_6566_ = crate::leanh::lean_ctor_get(v_x_6528_, 1);
                    crate::leanh::lean_inc_ref(v_b_6566_);
                    crate::leanh::lean_dec_ref_known(v_x_6528_, 2);
                    v___x_6567_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6565_);
                    v___x_6568_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_6569_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_6566_);
                    v___x_6570_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_6568_, v___x_6569_);
                    v___x_6571_ = l_Lean_Grind_CommRing_Poly_combine(v___x_6567_, v___x_6570_);
                    return v___x_6571_;
                }
                7 => {
                    v_a_6572_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    crate::leanh::lean_inc_ref(v_a_6572_);
                    v_b_6573_ = crate::leanh::lean_ctor_get(v_x_6528_, 1);
                    crate::leanh::lean_inc_ref(v_b_6573_);
                    crate::leanh::lean_dec_ref_known(v_x_6528_, 2);
                    v___x_6574_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6572_);
                    v___x_6575_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_6573_);
                    v___x_6576_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_6574_, v___x_6575_);
                    return v___x_6576_;
                }
                _ => {
                    v_a_6577_ = crate::leanh::lean_ctor_get(v_x_6528_, 0);
                    v_k_6578_ = crate::leanh::lean_ctor_get(v_x_6528_, 1);
                    v_isSharedCheck_6610_ = (!crate::leanh::lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6610_ == 0 {
                        v___x_6580_ = v_x_6528_;
                        v_isShared_6581_ = v_isSharedCheck_6610_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6578_);
                        crate::leanh::lean_inc(v_a_6577_);
                        crate::leanh::lean_dec(v_x_6528_);
                        v___x_6580_ = crate::leanh::lean_box(0);
                        v_isShared_6581_ = v_isSharedCheck_6610_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_6532_ == 0 {
                    v___x_6534_ = v___x_6531_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6535_, 0, v_k_6529_);
                    v___x_6534_ = v_reuseFailAlloc_6535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6534_;
            }
            3 => {
                v___x_6541_ = lean_nat_to_int(v_k_6537_);
                if v_isShared_6540_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6539_, 0);
                    crate::leanh::lean_ctor_set(v___x_6539_, 0, v___x_6541_);
                    v___x_6543_ = v___x_6539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6544_, 0, v___x_6541_);
                    v___x_6543_ = v_reuseFailAlloc_6544_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6543_;
            }
            5 => {
                if v_isShared_6549_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6548_, 0);
                    v___x_6551_ = v___x_6548_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6552_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_k_6546_);
                    v___x_6551_ = v_reuseFailAlloc_6552_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6551_;
            }
            7 => {
                v___x_6586_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6587_ = lean_nat_dec_eq(v_k_6578_, v___x_6586_);
                if v___x_6587_ == 0 {
                    match crate::leanh::lean_obj_tag(v_a_6577_) {
                        0 => {
                            crate::leanh::lean_del_object(v___x_6580_);
                            v_k_6588_ = crate::leanh::lean_ctor_get(v_a_6577_, 0);
                            crate::leanh::lean_inc(v_k_6588_);
                            crate::leanh::lean_dec_ref_known(v_a_6577_, 1);
                            v_n_6583_ = v_k_6588_;
                            state = 8;
                            continue;
                        }
                        2 => {
                            crate::leanh::lean_del_object(v___x_6580_);
                            v_k_6589_ = crate::leanh::lean_ctor_get(v_a_6577_, 0);
                            crate::leanh::lean_inc(v_k_6589_);
                            crate::leanh::lean_dec_ref_known(v_a_6577_, 1);
                            v_n_6583_ = v_k_6589_;
                            state = 8;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_del_object(v___x_6580_);
                            v_k_6590_ = crate::leanh::lean_ctor_get(v_a_6577_, 0);
                            v_isSharedCheck_6599_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6577_)) as u8;
                            if v_isSharedCheck_6599_ == 0 {
                                v___x_6592_ = v_a_6577_;
                                v_isShared_6593_ = v_isSharedCheck_6599_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_6590_);
                                crate::leanh::lean_dec(v_a_6577_);
                                v___x_6592_ = crate::leanh::lean_box(0);
                                v_isShared_6593_ = v_isSharedCheck_6599_;
                                state = 9;
                                continue;
                            }
                        }
                        3 => {
                            v_i_6600_ = crate::leanh::lean_ctor_get(v_a_6577_, 0);
                            crate::leanh::lean_inc(v_i_6600_);
                            crate::leanh::lean_dec_ref_known(v_a_6577_, 1);
                            if v_isShared_6581_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6580_, 0);
                                crate::leanh::lean_ctor_set(v___x_6580_, 0, v_i_6600_);
                                v___x_6602_ = v___x_6580_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_6606_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_i_6600_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6606_, 1, v_k_6578_);
                                v___x_6602_ = v_reuseFailAlloc_6606_;
                                state = 11;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_del_object(v___x_6580_);
                            v___x_6607_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6577_);
                            v___x_6608_ =
                                l_Lean_Grind_CommRing_Poly_pow__nc(v___x_6607_, v_k_6578_);
                            crate::leanh::lean_dec(v_k_6578_);
                            return v___x_6608_;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6580_);
                    crate::leanh::lean_dec(v_k_6578_);
                    crate::leanh::lean_dec_ref(v_a_6577_);
                    v___x_6609_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_6609_;
                }
            }
            8 => {
                v___x_6584_ = l_Int_pow(v_n_6583_, v_k_6578_);
                crate::leanh::lean_dec(v_k_6578_);
                crate::leanh::lean_dec(v_n_6583_);
                v___x_6585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6585_, 0, v___x_6584_);
                return v___x_6585_;
            }
            9 => {
                v___x_6594_ = lean_nat_to_int(v_k_6590_);
                v___x_6595_ = l_Int_pow(v___x_6594_, v_k_6578_);
                crate::leanh::lean_dec(v_k_6578_);
                crate::leanh::lean_dec(v___x_6594_);
                if v_isShared_6593_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6592_, 0);
                    crate::leanh::lean_ctor_set(v___x_6592_, 0, v___x_6595_);
                    v___x_6597_ = v___x_6592_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6595_);
                    v___x_6597_ = v_reuseFailAlloc_6598_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6597_;
            }
            11 => {
                v___x_6603_ = crate::leanh::lean_box(0);
                v___x_6604_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6604_, 0, v___x_6602_);
                crate::leanh::lean_ctor_set(v___x_6604_, 1, v___x_6603_);
                v___x_6605_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_6604_);
                return v___x_6605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_normEq0(
    mut v_p_6611_: *mut crate::leanh::LeanObject,
    mut v_c_6612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: u8 = 0;
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6624_: u8 = 0;
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: u8 = 0;
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_6611_) == 0 {
                    v_k_6613_ = crate::leanh::lean_ctor_get(v_p_6611_, 0);
                    v___x_6614_ = lean_nat_to_int(v_c_6612_);
                    v___x_6615_ = lean_int_emod(v_k_6613_, v___x_6614_);
                    crate::leanh::lean_dec(v___x_6614_);
                    v___x_6616_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v___x_6617_ = lean_int_dec_eq(v___x_6615_, v___x_6616_);
                    crate::leanh::lean_dec(v___x_6615_);
                    if v___x_6617_ == 0 {
                        return v_p_6611_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_p_6611_, 1);
                        v___x_6618_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        return v___x_6618_;
                    }
                } else {
                    v_k_6619_ = crate::leanh::lean_ctor_get(v_p_6611_, 0);
                    v_v_6620_ = crate::leanh::lean_ctor_get(v_p_6611_, 1);
                    v_p_6621_ = crate::leanh::lean_ctor_get(v_p_6611_, 2);
                    v_isSharedCheck_6634_ = (!crate::leanh::lean_is_exclusive(v_p_6611_)) as u8;
                    if v_isSharedCheck_6634_ == 0 {
                        v___x_6623_ = v_p_6611_;
                        v_isShared_6624_ = v_isSharedCheck_6634_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_6621_);
                        crate::leanh::lean_inc(v_v_6620_);
                        crate::leanh::lean_inc(v_k_6619_);
                        crate::leanh::lean_dec(v_p_6611_);
                        v___x_6623_ = crate::leanh::lean_box(0);
                        v_isShared_6624_ = v_isSharedCheck_6634_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_c_6612_);
                v___x_6625_ = lean_nat_to_int(v_c_6612_);
                v___x_6626_ = lean_int_emod(v_k_6619_, v___x_6625_);
                crate::leanh::lean_dec(v___x_6625_);
                v___x_6627_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6628_ = lean_int_dec_eq(v___x_6626_, v___x_6627_);
                crate::leanh::lean_dec(v___x_6626_);
                if v___x_6628_ == 0 {
                    v___x_6629_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_6621_, v_c_6612_);
                    if v_isShared_6624_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6623_, 2, v___x_6629_);
                        v___x_6631_ = v___x_6623_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6632_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_k_6619_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 1, v_v_6620_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 2, v___x_6629_);
                        v___x_6631_ = v_reuseFailAlloc_6632_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6623_);
                    crate::leanh::lean_dec(v_v_6620_);
                    crate::leanh::lean_dec(v_k_6619_);
                    v_p_6611_ = v_p_6621_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_6631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConstC(
    mut v_p_6635_: *mut crate::leanh::LeanObject,
    mut v_k_6636_: *mut crate::leanh::LeanObject,
    mut v_c_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6641_: u8 = 0;
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6648_: u8 = 0;
    let mut v_k_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6654_: u8 = 0;
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_6635_) == 0 {
                    v_k_6638_ = crate::leanh::lean_ctor_get(v_p_6635_, 0);
                    v_isSharedCheck_6648_ = (!crate::leanh::lean_is_exclusive(v_p_6635_)) as u8;
                    if v_isSharedCheck_6648_ == 0 {
                        v___x_6640_ = v_p_6635_;
                        v_isShared_6641_ = v_isSharedCheck_6648_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6638_);
                        crate::leanh::lean_dec(v_p_6635_);
                        v___x_6640_ = crate::leanh::lean_box(0);
                        v_isShared_6641_ = v_isSharedCheck_6648_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_6649_ = crate::leanh::lean_ctor_get(v_p_6635_, 0);
                    v_v_6650_ = crate::leanh::lean_ctor_get(v_p_6635_, 1);
                    v_p_6651_ = crate::leanh::lean_ctor_get(v_p_6635_, 2);
                    v_isSharedCheck_6659_ = (!crate::leanh::lean_is_exclusive(v_p_6635_)) as u8;
                    if v_isSharedCheck_6659_ == 0 {
                        v___x_6653_ = v_p_6635_;
                        v_isShared_6654_ = v_isSharedCheck_6659_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_6651_);
                        crate::leanh::lean_inc(v_v_6650_);
                        crate::leanh::lean_inc(v_k_6649_);
                        crate::leanh::lean_dec(v_p_6635_);
                        v___x_6653_ = crate::leanh::lean_box(0);
                        v_isShared_6654_ = v_isSharedCheck_6659_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6642_ = lean_int_add(v_k_6638_, v_k_6636_);
                crate::leanh::lean_dec(v_k_6638_);
                v___x_6643_ = lean_nat_to_int(v_c_6637_);
                v___x_6644_ = lean_int_emod(v___x_6642_, v___x_6643_);
                crate::leanh::lean_dec(v___x_6643_);
                crate::leanh::lean_dec(v___x_6642_);
                if v_isShared_6641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6640_, 0, v___x_6644_);
                    v___x_6646_ = v___x_6640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6647_, 0, v___x_6644_);
                    v___x_6646_ = v_reuseFailAlloc_6647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6646_;
            }
            3 => {
                v___x_6655_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_6651_, v_k_6636_, v_c_6637_);
                if v_isShared_6654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6653_, 2, v___x_6655_);
                    v___x_6657_ = v___x_6653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6658_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6658_, 0, v_k_6649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6658_, 1, v_v_6650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6658_, 2, v___x_6655_);
                    v___x_6657_ = v_reuseFailAlloc_6658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConstC___boxed(
    mut v_p_6660_: *mut crate::leanh::LeanObject,
    mut v_k_6661_: *mut crate::leanh::LeanObject,
    mut v_c_6662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6663_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_6660_, v_k_6661_, v_c_6662_);
    crate::leanh::lean_dec(v_k_6661_);
    return v_res_6663_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insertC_go(
    mut v_m_6664_: *mut crate::leanh::LeanObject,
    mut v_c_6665_: *mut crate::leanh::LeanObject,
    mut v_k_6666_: *mut crate::leanh::LeanObject,
    mut v_a_6667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: u8 = 0;
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6675_: u8 = 0;
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6680_: u8 = 0;
    let mut v_unused_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_x27_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: u8 = 0;
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6695_: u8 = 0;
    let mut v_unused_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6667_) == 0 {
                    crate::leanh::lean_dec(v_c_6665_);
                    v___x_6668_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6668_, 0, v_k_6666_);
                    crate::leanh::lean_ctor_set(v___x_6668_, 1, v_m_6664_);
                    crate::leanh::lean_ctor_set(v___x_6668_, 2, v_a_6667_);
                    return v___x_6668_;
                } else {
                    v_k_6669_ = crate::leanh::lean_ctor_get(v_a_6667_, 0);
                    v_v_6670_ = crate::leanh::lean_ctor_get(v_a_6667_, 1);
                    v_p_6671_ = crate::leanh::lean_ctor_get(v_a_6667_, 2);
                    v___x_6672_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_6664_, v_v_6670_);
                    match v___x_6672_ {
                        0 => {
                            crate::leanh::lean_inc_ref(v_p_6671_);
                            crate::leanh::lean_inc(v_v_6670_);
                            crate::leanh::lean_inc(v_k_6669_);
                            v_isSharedCheck_6680_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6667_)) as u8;
                            if v_isSharedCheck_6680_ == 0 {
                                v_unused_6681_ = crate::leanh::lean_ctor_get(v_a_6667_, 2);
                                crate::leanh::lean_dec(v_unused_6681_);
                                v_unused_6682_ = crate::leanh::lean_ctor_get(v_a_6667_, 1);
                                crate::leanh::lean_dec(v_unused_6682_);
                                v_unused_6683_ = crate::leanh::lean_ctor_get(v_a_6667_, 0);
                                crate::leanh::lean_dec(v_unused_6683_);
                                v___x_6674_ = v_a_6667_;
                                v_isShared_6675_ = v_isSharedCheck_6680_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6667_);
                                v___x_6674_ = crate::leanh::lean_box(0);
                                v_isShared_6675_ = v_isSharedCheck_6680_;
                                state = 1;
                                continue;
                            }
                        }
                        1 => {
                            crate::leanh::lean_inc_ref(v_p_6671_);
                            crate::leanh::lean_inc(v_k_6669_);
                            v_isSharedCheck_6695_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6667_)) as u8;
                            if v_isSharedCheck_6695_ == 0 {
                                v_unused_6696_ = crate::leanh::lean_ctor_get(v_a_6667_, 2);
                                crate::leanh::lean_dec(v_unused_6696_);
                                v_unused_6697_ = crate::leanh::lean_ctor_get(v_a_6667_, 1);
                                crate::leanh::lean_dec(v_unused_6697_);
                                v_unused_6698_ = crate::leanh::lean_ctor_get(v_a_6667_, 0);
                                crate::leanh::lean_dec(v_unused_6698_);
                                v___x_6685_ = v_a_6667_;
                                v_isShared_6686_ = v_isSharedCheck_6695_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6667_);
                                v___x_6685_ = crate::leanh::lean_box(0);
                                v_isShared_6686_ = v_isSharedCheck_6695_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_c_6665_);
                            v___x_6699_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6699_, 0, v_k_6666_);
                            crate::leanh::lean_ctor_set(v___x_6699_, 1, v_m_6664_);
                            crate::leanh::lean_ctor_set(v___x_6699_, 2, v_a_6667_);
                            return v___x_6699_;
                        }
                    }
                }
            }
            1 => {
                v___x_6676_ = l_Lean_Grind_CommRing_Poly_insertC_go(
                    v_m_6664_, v_c_6665_, v_k_6666_, v_p_6671_,
                );
                if v_isShared_6675_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6674_, 2, v___x_6676_);
                    v___x_6678_ = v___x_6674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6679_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_k_6669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6679_, 1, v_v_6670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6679_, 2, v___x_6676_);
                    v___x_6678_ = v_reuseFailAlloc_6679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6678_;
            }
            3 => {
                v___x_6687_ = lean_int_add(v_k_6666_, v_k_6669_);
                crate::leanh::lean_dec(v_k_6669_);
                crate::leanh::lean_dec(v_k_6666_);
                v___x_6688_ = lean_nat_to_int(v_c_6665_);
                v_k_x27_x27_6689_ = lean_int_emod(v___x_6687_, v___x_6688_);
                crate::leanh::lean_dec(v___x_6688_);
                crate::leanh::lean_dec(v___x_6687_);
                v___x_6690_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6691_ = lean_int_dec_eq(v_k_x27_x27_6689_, v___x_6690_);
                if v___x_6691_ == 0 {
                    if v_isShared_6686_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6685_, 1, v_m_6664_);
                        crate::leanh::lean_ctor_set(v___x_6685_, 0, v_k_x27_x27_6689_);
                        v___x_6693_ = v___x_6685_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6694_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_k_x27_x27_6689_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 1, v_m_6664_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 2, v_p_6671_);
                        v___x_6693_ = v_reuseFailAlloc_6694_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_x27_x27_6689_);
                    crate::leanh::lean_del_object(v___x_6685_);
                    crate::leanh::lean_dec(v_m_6664_);
                    return v_p_6671_;
                }
            }
            4 => {
                return v___x_6693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insertC(
    mut v_k_6700_: *mut crate::leanh::LeanObject,
    mut v_m_6701_: *mut crate::leanh::LeanObject,
    mut v_p_6702_: *mut crate::leanh::LeanObject,
    mut v_c_6703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: u8 = 0;
    crate::leanh::lean_inc(v_c_6703_);
    v___x_6704_ = lean_nat_to_int(v_c_6703_);
    v_k_6705_ = lean_int_emod(v_k_6700_, v___x_6704_);
    crate::leanh::lean_dec(v___x_6704_);
    v___x_6706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6707_ = lean_int_dec_eq(v_k_6705_, v___x_6706_);
    if v___x_6707_ == 0 {
        let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6708_ =
            l_Lean_Grind_CommRing_Poly_insertC_go(v_m_6701_, v_c_6703_, v_k_6705_, v_p_6702_);
        return v___x_6708_;
    } else {
        crate::leanh::lean_dec(v_k_6705_);
        crate::leanh::lean_dec(v_c_6703_);
        crate::leanh::lean_dec(v_m_6701_);
        return v_p_6702_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insertC___boxed(
    mut v_k_6709_: *mut crate::leanh::LeanObject,
    mut v_m_6710_: *mut crate::leanh::LeanObject,
    mut v_p_6711_: *mut crate::leanh::LeanObject,
    mut v_c_6712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6713_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_6709_, v_m_6710_, v_p_6711_, v_c_6712_);
    crate::leanh::lean_dec(v_k_6709_);
    return v_res_6713_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstC_go(
    mut v_k_6714_: *mut crate::leanh::LeanObject,
    mut v_c_6715_: *mut crate::leanh::LeanObject,
    mut v_a_6716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6720_: u8 = 0;
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6727_: u8 = 0;
    let mut v_k_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6733_: u8 = 0;
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: u8 = 0;
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6716_) == 0 {
                    v_k_6717_ = crate::leanh::lean_ctor_get(v_a_6716_, 0);
                    v_isSharedCheck_6727_ = (!crate::leanh::lean_is_exclusive(v_a_6716_)) as u8;
                    if v_isSharedCheck_6727_ == 0 {
                        v___x_6719_ = v_a_6716_;
                        v_isShared_6720_ = v_isSharedCheck_6727_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6717_);
                        crate::leanh::lean_dec(v_a_6716_);
                        v___x_6719_ = crate::leanh::lean_box(0);
                        v_isShared_6720_ = v_isSharedCheck_6727_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_6728_ = crate::leanh::lean_ctor_get(v_a_6716_, 0);
                    v_v_6729_ = crate::leanh::lean_ctor_get(v_a_6716_, 1);
                    v_p_6730_ = crate::leanh::lean_ctor_get(v_a_6716_, 2);
                    v_isSharedCheck_6744_ = (!crate::leanh::lean_is_exclusive(v_a_6716_)) as u8;
                    if v_isSharedCheck_6744_ == 0 {
                        v___x_6732_ = v_a_6716_;
                        v_isShared_6733_ = v_isSharedCheck_6744_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_6730_);
                        crate::leanh::lean_inc(v_v_6729_);
                        crate::leanh::lean_inc(v_k_6728_);
                        crate::leanh::lean_dec(v_a_6716_);
                        v___x_6732_ = crate::leanh::lean_box(0);
                        v_isShared_6733_ = v_isSharedCheck_6744_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6721_ = lean_int_mul(v_k_6714_, v_k_6717_);
                crate::leanh::lean_dec(v_k_6717_);
                v___x_6722_ = lean_nat_to_int(v_c_6715_);
                v___x_6723_ = lean_int_emod(v___x_6721_, v___x_6722_);
                crate::leanh::lean_dec(v___x_6722_);
                crate::leanh::lean_dec(v___x_6721_);
                if v_isShared_6720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6719_, 0, v___x_6723_);
                    v___x_6725_ = v___x_6719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6726_, 0, v___x_6723_);
                    v___x_6725_ = v_reuseFailAlloc_6726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6725_;
            }
            3 => {
                v___x_6734_ = lean_int_mul(v_k_6714_, v_k_6728_);
                crate::leanh::lean_dec(v_k_6728_);
                crate::leanh::lean_inc(v_c_6715_);
                v___x_6735_ = lean_nat_to_int(v_c_6715_);
                v_k_6736_ = lean_int_emod(v___x_6734_, v___x_6735_);
                crate::leanh::lean_dec(v___x_6735_);
                crate::leanh::lean_dec(v___x_6734_);
                v___x_6737_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6738_ = lean_int_dec_eq(v_k_6736_, v___x_6737_);
                if v___x_6738_ == 0 {
                    v___x_6739_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_6714_, v_c_6715_, v_p_6730_);
                    if v_isShared_6733_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6732_, 2, v___x_6739_);
                        crate::leanh::lean_ctor_set(v___x_6732_, 0, v_k_6736_);
                        v___x_6741_ = v___x_6732_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6742_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_k_6736_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 1, v_v_6729_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 2, v___x_6739_);
                        v___x_6741_ = v_reuseFailAlloc_6742_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6736_);
                    crate::leanh::lean_del_object(v___x_6732_);
                    crate::leanh::lean_dec(v_v_6729_);
                    v_a_6716_ = v_p_6730_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                return v___x_6741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(
    mut v_k_6745_: *mut crate::leanh::LeanObject,
    mut v_c_6746_: *mut crate::leanh::LeanObject,
    mut v_a_6747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6748_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_6745_, v_c_6746_, v_a_6747_);
    crate::leanh::lean_dec(v_k_6745_);
    return v_res_6748_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstC(
    mut v_k_6749_: *mut crate::leanh::LeanObject,
    mut v_p_6750_: *mut crate::leanh::LeanObject,
    mut v_c_6751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: u8 = 0;
    crate::leanh::lean_inc(v_c_6751_);
    v___x_6752_ = lean_nat_to_int(v_c_6751_);
    v_k_6753_ = lean_int_emod(v_k_6749_, v___x_6752_);
    crate::leanh::lean_dec(v___x_6752_);
    v___x_6754_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6755_ = lean_int_dec_eq(v_k_6753_, v___x_6754_);
    if v___x_6755_ == 0 {
        let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6757_: u8 = 0;
        v___x_6756_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_6757_ = lean_int_dec_eq(v_k_6753_, v___x_6756_);
        crate::leanh::lean_dec(v_k_6753_);
        if v___x_6757_ == 0 {
            let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6758_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_6749_, v_c_6751_, v_p_6750_);
            return v___x_6758_;
        } else {
            crate::leanh::lean_dec(v_c_6751_);
            return v_p_6750_;
        }
    } else {
        let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_6753_);
        crate::leanh::lean_dec(v_c_6751_);
        crate::leanh::lean_dec_ref(v_p_6750_);
        v___x_6759_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
        );
        return v___x_6759_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstC___boxed(
    mut v_k_6760_: *mut crate::leanh::LeanObject,
    mut v_p_6761_: *mut crate::leanh::LeanObject,
    mut v_c_6762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6763_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6760_, v_p_6761_, v_c_6762_);
    crate::leanh::lean_dec(v_k_6760_);
    return v_res_6763_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC_go(
    mut v_k_6764_: *mut crate::leanh::LeanObject,
    mut v_m_6765_: *mut crate::leanh::LeanObject,
    mut v_c_6766_: *mut crate::leanh::LeanObject,
    mut v_a_6767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: u8 = 0;
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: u8 = 0;
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6767_) == 0 {
                    v_k_6768_ = crate::leanh::lean_ctor_get(v_a_6767_, 0);
                    crate::leanh::lean_inc(v_k_6768_);
                    crate::leanh::lean_dec_ref_known(v_a_6767_, 1);
                    v___x_6769_ = lean_int_mul(v_k_6764_, v_k_6768_);
                    crate::leanh::lean_dec(v_k_6768_);
                    v___x_6770_ = lean_nat_to_int(v_c_6766_);
                    v_k_6771_ = lean_int_emod(v___x_6769_, v___x_6770_);
                    crate::leanh::lean_dec(v___x_6770_);
                    crate::leanh::lean_dec(v___x_6769_);
                    v___x_6772_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v___x_6773_ = lean_int_dec_eq(v_k_6771_, v___x_6772_);
                    if v___x_6773_ == 0 {
                        v___x_6774_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        v___x_6775_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6775_, 0, v_k_6771_);
                        crate::leanh::lean_ctor_set(v___x_6775_, 1, v_m_6765_);
                        crate::leanh::lean_ctor_set(v___x_6775_, 2, v___x_6774_);
                        return v___x_6775_;
                    } else {
                        crate::leanh::lean_dec(v_k_6771_);
                        crate::leanh::lean_dec(v_m_6765_);
                        v___x_6776_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        return v___x_6776_;
                    }
                } else {
                    v_k_6777_ = crate::leanh::lean_ctor_get(v_a_6767_, 0);
                    v_v_6778_ = crate::leanh::lean_ctor_get(v_a_6767_, 1);
                    v_p_6779_ = crate::leanh::lean_ctor_get(v_a_6767_, 2);
                    v_isSharedCheck_6794_ = (!crate::leanh::lean_is_exclusive(v_a_6767_)) as u8;
                    if v_isSharedCheck_6794_ == 0 {
                        v___x_6781_ = v_a_6767_;
                        v_isShared_6782_ = v_isSharedCheck_6794_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_6779_);
                        crate::leanh::lean_inc(v_v_6778_);
                        crate::leanh::lean_inc(v_k_6777_);
                        crate::leanh::lean_dec(v_a_6767_);
                        v___x_6781_ = crate::leanh::lean_box(0);
                        v_isShared_6782_ = v_isSharedCheck_6794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6783_ = lean_int_mul(v_k_6764_, v_k_6777_);
                crate::leanh::lean_dec(v_k_6777_);
                crate::leanh::lean_inc(v_c_6766_);
                v___x_6784_ = lean_nat_to_int(v_c_6766_);
                v_k_6785_ = lean_int_emod(v___x_6783_, v___x_6784_);
                crate::leanh::lean_dec(v___x_6784_);
                crate::leanh::lean_dec(v___x_6783_);
                v___x_6786_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6787_ = lean_int_dec_eq(v_k_6785_, v___x_6786_);
                if v___x_6787_ == 0 {
                    crate::leanh::lean_inc(v_m_6765_);
                    v___x_6788_ = l_Lean_Grind_CommRing_Mon_mul(v_m_6765_, v_v_6778_);
                    v___x_6789_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(
                        v_k_6764_, v_m_6765_, v_c_6766_, v_p_6779_,
                    );
                    if v_isShared_6782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6781_, 2, v___x_6789_);
                        crate::leanh::lean_ctor_set(v___x_6781_, 1, v___x_6788_);
                        crate::leanh::lean_ctor_set(v___x_6781_, 0, v_k_6785_);
                        v___x_6791_ = v___x_6781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6792_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6792_, 0, v_k_6785_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6792_, 1, v___x_6788_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6792_, 2, v___x_6789_);
                        v___x_6791_ = v_reuseFailAlloc_6792_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6785_);
                    crate::leanh::lean_del_object(v___x_6781_);
                    crate::leanh::lean_dec(v_v_6778_);
                    v_a_6767_ = v_p_6779_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_6791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(
    mut v_k_6795_: *mut crate::leanh::LeanObject,
    mut v_m_6796_: *mut crate::leanh::LeanObject,
    mut v_c_6797_: *mut crate::leanh::LeanObject,
    mut v_a_6798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6799_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_6795_, v_m_6796_, v_c_6797_, v_a_6798_);
    crate::leanh::lean_dec(v_k_6795_);
    return v_res_6799_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC(
    mut v_k_6800_: *mut crate::leanh::LeanObject,
    mut v_m_6801_: *mut crate::leanh::LeanObject,
    mut v_p_6802_: *mut crate::leanh::LeanObject,
    mut v_c_6803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    crate::leanh::lean_inc(v_c_6803_);
    v___x_6804_ = lean_nat_to_int(v_c_6803_);
    v_k_6805_ = lean_int_emod(v_k_6800_, v___x_6804_);
    crate::leanh::lean_dec(v___x_6804_);
    v___x_6806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6807_ = lean_int_dec_eq(v_k_6805_, v___x_6806_);
    if v___x_6807_ == 0 {
        let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6809_: u8 = 0;
        v___x_6808_ = crate::leanh::lean_box(0);
        v___x_6809_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6801_, v___x_6808_);
        if v___x_6809_ == 0 {
            let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_6805_);
            v___x_6810_ =
                l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_6800_, v_m_6801_, v_c_6803_, v_p_6802_);
            return v___x_6810_;
        } else {
            let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_m_6801_);
            v___x_6811_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6805_, v_p_6802_, v_c_6803_);
            crate::leanh::lean_dec(v_k_6805_);
            return v___x_6811_;
        }
    } else {
        let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_6805_);
        crate::leanh::lean_dec(v_c_6803_);
        crate::leanh::lean_dec_ref(v_p_6802_);
        crate::leanh::lean_dec(v_m_6801_);
        v___x_6812_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
        );
        return v___x_6812_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC___boxed(
    mut v_k_6813_: *mut crate::leanh::LeanObject,
    mut v_m_6814_: *mut crate::leanh::LeanObject,
    mut v_p_6815_: *mut crate::leanh::LeanObject,
    mut v_c_6816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6817_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_6813_, v_m_6814_, v_p_6815_, v_c_6816_);
    crate::leanh::lean_dec(v_k_6813_);
    return v_res_6817_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(
    mut v_k_6818_: *mut crate::leanh::LeanObject,
    mut v_m_6819_: *mut crate::leanh::LeanObject,
    mut v_c_6820_: *mut crate::leanh::LeanObject,
    mut v_p_6821_: *mut crate::leanh::LeanObject,
    mut v_acc_6822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_6821_) == 0 {
                    v_k_6823_ = crate::leanh::lean_ctor_get(v_p_6821_, 0);
                    crate::leanh::lean_inc(v_k_6823_);
                    crate::leanh::lean_dec_ref_known(v_p_6821_, 1);
                    v___x_6824_ = lean_int_mul(v_k_6818_, v_k_6823_);
                    crate::leanh::lean_dec(v_k_6823_);
                    v___x_6825_ = lean_nat_to_int(v_c_6820_);
                    v___x_6826_ = lean_int_emod(v___x_6824_, v___x_6825_);
                    crate::leanh::lean_dec(v___x_6825_);
                    crate::leanh::lean_dec(v___x_6824_);
                    v___x_6827_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6826_, v_m_6819_, v_acc_6822_);
                    return v___x_6827_;
                } else {
                    v_k_6828_ = crate::leanh::lean_ctor_get(v_p_6821_, 0);
                    crate::leanh::lean_inc(v_k_6828_);
                    v_v_6829_ = crate::leanh::lean_ctor_get(v_p_6821_, 1);
                    crate::leanh::lean_inc(v_v_6829_);
                    v_p_6830_ = crate::leanh::lean_ctor_get(v_p_6821_, 2);
                    crate::leanh::lean_inc_ref(v_p_6830_);
                    crate::leanh::lean_dec_ref_known(v_p_6821_, 3);
                    v___x_6831_ = lean_int_mul(v_k_6818_, v_k_6828_);
                    crate::leanh::lean_dec(v_k_6828_);
                    crate::leanh::lean_inc(v_c_6820_);
                    v___x_6832_ = lean_nat_to_int(v_c_6820_);
                    v___x_6833_ = lean_int_emod(v___x_6831_, v___x_6832_);
                    crate::leanh::lean_dec(v___x_6832_);
                    crate::leanh::lean_dec(v___x_6831_);
                    crate::leanh::lean_inc(v_m_6819_);
                    v___x_6834_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_6819_, v_v_6829_);
                    v___x_6835_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6833_, v___x_6834_, v_acc_6822_);
                    v_p_6821_ = v_p_6830_;
                    v_acc_6822_ = v___x_6835_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(
    mut v_k_6837_: *mut crate::leanh::LeanObject,
    mut v_m_6838_: *mut crate::leanh::LeanObject,
    mut v_c_6839_: *mut crate::leanh::LeanObject,
    mut v_p_6840_: *mut crate::leanh::LeanObject,
    mut v_acc_6841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6842_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(
        v_k_6837_,
        v_m_6838_,
        v_c_6839_,
        v_p_6840_,
        v_acc_6841_,
    );
    crate::leanh::lean_dec(v_k_6837_);
    return v_res_6842_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC__nc(
    mut v_k_6843_: *mut crate::leanh::LeanObject,
    mut v_m_6844_: *mut crate::leanh::LeanObject,
    mut v_p_6845_: *mut crate::leanh::LeanObject,
    mut v_c_6846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u8 = 0;
    crate::leanh::lean_inc(v_c_6846_);
    v___x_6847_ = lean_nat_to_int(v_c_6846_);
    v_k_6848_ = lean_int_emod(v_k_6843_, v___x_6847_);
    crate::leanh::lean_dec(v___x_6847_);
    v___x_6849_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6850_ = lean_int_dec_eq(v_k_6848_, v___x_6849_);
    if v___x_6850_ == 0 {
        let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6852_: u8 = 0;
        v___x_6851_ = crate::leanh::lean_box(0);
        v___x_6852_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6844_, v___x_6851_);
        if v___x_6852_ == 0 {
            let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_6848_);
            v___x_6853_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                ),
                _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
            );
            v___x_6854_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(
                v_k_6843_,
                v_m_6844_,
                v_c_6846_,
                v_p_6845_,
                v___x_6853_,
            );
            return v___x_6854_;
        } else {
            let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_m_6844_);
            v___x_6855_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6848_, v_p_6845_, v_c_6846_);
            crate::leanh::lean_dec(v_k_6848_);
            return v___x_6855_;
        }
    } else {
        let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_6848_);
        crate::leanh::lean_dec(v_c_6846_);
        crate::leanh::lean_dec_ref(v_p_6845_);
        crate::leanh::lean_dec(v_m_6844_);
        v___x_6856_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
        );
        return v___x_6856_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(
    mut v_k_6857_: *mut crate::leanh::LeanObject,
    mut v_m_6858_: *mut crate::leanh::LeanObject,
    mut v_p_6859_: *mut crate::leanh::LeanObject,
    mut v_c_6860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6861_ =
        l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_6857_, v_m_6858_, v_p_6859_, v_c_6860_);
    crate::leanh::lean_dec(v_k_6857_);
    return v_res_6861_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combineC(
    mut v_p_u2081_6862_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6863_: *mut crate::leanh::LeanObject,
    mut v_c_6864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6869_: u8 = 0;
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6876_: u8 = 0;
    let mut v_k_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: u8 = 0;
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6890_: u8 = 0;
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6895_: u8 = 0;
    let mut v_unused_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6901_: u8 = 0;
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: u8 = 0;
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6912_: u8 = 0;
    let mut v_unused_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6923_: u8 = 0;
    let mut v_unused_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_6862_) == 0 {
                    if crate::leanh::lean_obj_tag(v_p_u2082_6863_) == 0 {
                        v_k_6865_ = crate::leanh::lean_ctor_get(v_p_u2081_6862_, 0);
                        crate::leanh::lean_inc(v_k_6865_);
                        crate::leanh::lean_dec_ref_known(v_p_u2081_6862_, 1);
                        v_k_6866_ = crate::leanh::lean_ctor_get(v_p_u2082_6863_, 0);
                        v_isSharedCheck_6876_ =
                            (!crate::leanh::lean_is_exclusive(v_p_u2082_6863_)) as u8;
                        if v_isSharedCheck_6876_ == 0 {
                            v___x_6868_ = v_p_u2082_6863_;
                            v_isShared_6869_ = v_isSharedCheck_6876_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_6866_);
                            crate::leanh::lean_dec(v_p_u2082_6863_);
                            v___x_6868_ = crate::leanh::lean_box(0);
                            v_isShared_6869_ = v_isSharedCheck_6876_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_k_6877_ = crate::leanh::lean_ctor_get(v_p_u2081_6862_, 0);
                        crate::leanh::lean_inc(v_k_6877_);
                        crate::leanh::lean_dec_ref_known(v_p_u2081_6862_, 1);
                        v___x_6878_ = l_Lean_Grind_CommRing_Poly_addConstC(
                            v_p_u2082_6863_,
                            v_k_6877_,
                            v_c_6864_,
                        );
                        crate::leanh::lean_dec(v_k_6877_);
                        return v___x_6878_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_p_u2082_6863_) == 0 {
                        v_k_6879_ = crate::leanh::lean_ctor_get(v_p_u2082_6863_, 0);
                        crate::leanh::lean_inc(v_k_6879_);
                        crate::leanh::lean_dec_ref_known(v_p_u2082_6863_, 1);
                        v___x_6880_ = l_Lean_Grind_CommRing_Poly_addConstC(
                            v_p_u2081_6862_,
                            v_k_6879_,
                            v_c_6864_,
                        );
                        crate::leanh::lean_dec(v_k_6879_);
                        return v___x_6880_;
                    } else {
                        v_k_6881_ = crate::leanh::lean_ctor_get(v_p_u2081_6862_, 0);
                        v_v_6882_ = crate::leanh::lean_ctor_get(v_p_u2081_6862_, 1);
                        v_p_6883_ = crate::leanh::lean_ctor_get(v_p_u2081_6862_, 2);
                        v_k_6884_ = crate::leanh::lean_ctor_get(v_p_u2082_6863_, 0);
                        v_v_6885_ = crate::leanh::lean_ctor_get(v_p_u2082_6863_, 1);
                        v_p_6886_ = crate::leanh::lean_ctor_get(v_p_u2082_6863_, 2);
                        v___x_6887_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_6882_, v_v_6885_);
                        match v___x_6887_ {
                            0 => {
                                crate::leanh::lean_inc_ref(v_p_6886_);
                                crate::leanh::lean_inc(v_v_6885_);
                                crate::leanh::lean_inc(v_k_6884_);
                                v_isSharedCheck_6895_ =
                                    (!crate::leanh::lean_is_exclusive(v_p_u2082_6863_)) as u8;
                                if v_isSharedCheck_6895_ == 0 {
                                    v_unused_6896_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_6863_, 2);
                                    crate::leanh::lean_dec(v_unused_6896_);
                                    v_unused_6897_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_6863_, 1);
                                    crate::leanh::lean_dec(v_unused_6897_);
                                    v_unused_6898_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_6863_, 0);
                                    crate::leanh::lean_dec(v_unused_6898_);
                                    v___x_6889_ = v_p_u2082_6863_;
                                    v_isShared_6890_ = v_isSharedCheck_6895_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_p_u2082_6863_);
                                    v___x_6889_ = crate::leanh::lean_box(0);
                                    v_isShared_6890_ = v_isSharedCheck_6895_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                crate::leanh::lean_inc_ref(v_p_6886_);
                                crate::leanh::lean_inc(v_k_6884_);
                                crate::leanh::lean_inc_ref(v_p_6883_);
                                crate::leanh::lean_inc(v_v_6882_);
                                crate::leanh::lean_inc(v_k_6881_);
                                crate::leanh::lean_dec_ref_known(v_p_u2081_6862_, 3);
                                v_isSharedCheck_6912_ =
                                    (!crate::leanh::lean_is_exclusive(v_p_u2082_6863_)) as u8;
                                if v_isSharedCheck_6912_ == 0 {
                                    v_unused_6913_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_6863_, 2);
                                    crate::leanh::lean_dec(v_unused_6913_);
                                    v_unused_6914_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_6863_, 1);
                                    crate::leanh::lean_dec(v_unused_6914_);
                                    v_unused_6915_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_6863_, 0);
                                    crate::leanh::lean_dec(v_unused_6915_);
                                    v___x_6900_ = v_p_u2082_6863_;
                                    v_isShared_6901_ = v_isSharedCheck_6912_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_p_u2082_6863_);
                                    v___x_6900_ = crate::leanh::lean_box(0);
                                    v_isShared_6901_ = v_isSharedCheck_6912_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                crate::leanh::lean_inc_ref(v_p_6883_);
                                crate::leanh::lean_inc(v_v_6882_);
                                crate::leanh::lean_inc(v_k_6881_);
                                v_isSharedCheck_6923_ =
                                    (!crate::leanh::lean_is_exclusive(v_p_u2081_6862_)) as u8;
                                if v_isSharedCheck_6923_ == 0 {
                                    v_unused_6924_ =
                                        crate::leanh::lean_ctor_get(v_p_u2081_6862_, 2);
                                    crate::leanh::lean_dec(v_unused_6924_);
                                    v_unused_6925_ =
                                        crate::leanh::lean_ctor_get(v_p_u2081_6862_, 1);
                                    crate::leanh::lean_dec(v_unused_6925_);
                                    v_unused_6926_ =
                                        crate::leanh::lean_ctor_get(v_p_u2081_6862_, 0);
                                    crate::leanh::lean_dec(v_unused_6926_);
                                    v___x_6917_ = v_p_u2081_6862_;
                                    v_isShared_6918_ = v_isSharedCheck_6923_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_p_u2081_6862_);
                                    v___x_6917_ = crate::leanh::lean_box(0);
                                    v_isShared_6918_ = v_isSharedCheck_6923_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6870_ = lean_int_add(v_k_6865_, v_k_6866_);
                crate::leanh::lean_dec(v_k_6866_);
                crate::leanh::lean_dec(v_k_6865_);
                v___x_6871_ = lean_nat_to_int(v_c_6864_);
                v___x_6872_ = lean_int_emod(v___x_6870_, v___x_6871_);
                crate::leanh::lean_dec(v___x_6871_);
                crate::leanh::lean_dec(v___x_6870_);
                if v_isShared_6869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6868_, 0, v___x_6872_);
                    v___x_6874_ = v___x_6868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6875_, 0, v___x_6872_);
                    v___x_6874_ = v_reuseFailAlloc_6875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6874_;
            }
            3 => {
                v___x_6891_ =
                    l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_6862_, v_p_6886_, v_c_6864_);
                if v_isShared_6890_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6889_, 2, v___x_6891_);
                    v___x_6893_ = v___x_6889_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6894_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6894_, 0, v_k_6884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6894_, 1, v_v_6885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6894_, 2, v___x_6891_);
                    v___x_6893_ = v_reuseFailAlloc_6894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6893_;
            }
            5 => {
                v___x_6902_ = lean_int_add(v_k_6881_, v_k_6884_);
                crate::leanh::lean_dec(v_k_6884_);
                crate::leanh::lean_dec(v_k_6881_);
                crate::leanh::lean_inc(v_c_6864_);
                v___x_6903_ = lean_nat_to_int(v_c_6864_);
                v_k_6904_ = lean_int_emod(v___x_6902_, v___x_6903_);
                crate::leanh::lean_dec(v___x_6903_);
                crate::leanh::lean_dec(v___x_6902_);
                v___x_6905_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6906_ = lean_int_dec_eq(v_k_6904_, v___x_6905_);
                if v___x_6906_ == 0 {
                    v___x_6907_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_p_6883_, v_p_6886_, v_c_6864_);
                    if v_isShared_6901_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6900_, 2, v___x_6907_);
                        crate::leanh::lean_ctor_set(v___x_6900_, 1, v_v_6882_);
                        crate::leanh::lean_ctor_set(v___x_6900_, 0, v_k_6904_);
                        v___x_6909_ = v___x_6900_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6910_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 0, v_k_6904_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 1, v_v_6882_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 2, v___x_6907_);
                        v___x_6909_ = v_reuseFailAlloc_6910_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6904_);
                    crate::leanh::lean_del_object(v___x_6900_);
                    crate::leanh::lean_dec(v_v_6882_);
                    v_p_u2081_6862_ = v_p_6883_;
                    v_p_u2082_6863_ = v_p_6886_;
                    state = 0;
                    continue;
                }
            }
            6 => {
                return v___x_6909_;
            }
            7 => {
                v___x_6919_ =
                    l_Lean_Grind_CommRing_Poly_combineC(v_p_6883_, v_p_u2082_6863_, v_c_6864_);
                if v_isShared_6918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6917_, 2, v___x_6919_);
                    v___x_6921_ = v___x_6917_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6922_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_k_6881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 1, v_v_6882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 2, v___x_6919_);
                    v___x_6921_ = v_reuseFailAlloc_6922_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulC_go(
    mut v_p_u2082_6927_: *mut crate::leanh::LeanObject,
    mut v_c_6928_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_6929_: *mut crate::leanh::LeanObject,
    mut v_acc_6930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_6929_) == 0 {
                    v_k_6931_ = crate::leanh::lean_ctor_get(v_p_u2081_6929_, 0);
                    crate::leanh::lean_inc(v_k_6931_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6929_, 1);
                    crate::leanh::lean_inc(v_c_6928_);
                    v___x_6932_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6931_, v_p_u2082_6927_, v_c_6928_);
                    crate::leanh::lean_dec(v_k_6931_);
                    v___x_6933_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_acc_6930_, v___x_6932_, v_c_6928_);
                    return v___x_6933_;
                } else {
                    v_k_6934_ = crate::leanh::lean_ctor_get(v_p_u2081_6929_, 0);
                    crate::leanh::lean_inc(v_k_6934_);
                    v_v_6935_ = crate::leanh::lean_ctor_get(v_p_u2081_6929_, 1);
                    crate::leanh::lean_inc(v_v_6935_);
                    v_p_6936_ = crate::leanh::lean_ctor_get(v_p_u2081_6929_, 2);
                    crate::leanh::lean_inc_ref(v_p_6936_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6929_, 3);
                    crate::leanh::lean_inc_n(v_c_6928_, 2);
                    crate::leanh::lean_inc_ref(v_p_u2082_6927_);
                    v___x_6937_ = l_Lean_Grind_CommRing_Poly_mulMonC(
                        v_k_6934_,
                        v_v_6935_,
                        v_p_u2082_6927_,
                        v_c_6928_,
                    );
                    crate::leanh::lean_dec(v_k_6934_);
                    v___x_6938_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_acc_6930_, v___x_6937_, v_c_6928_);
                    v_p_u2081_6929_ = v_p_6936_;
                    v_acc_6930_ = v___x_6938_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulC(
    mut v_p_u2081_6940_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6941_: *mut crate::leanh::LeanObject,
    mut v_c_6942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6943_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6944_ = l_Lean_Grind_CommRing_Poly_mulC_go(
        v_p_u2082_6941_,
        v_c_6942_,
        v_p_u2081_6940_,
        v___x_6943_,
    );
    return v___x_6944_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulC__nc_go(
    mut v_p_u2082_6945_: *mut crate::leanh::LeanObject,
    mut v_c_6946_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_6947_: *mut crate::leanh::LeanObject,
    mut v_acc_6948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_6947_) == 0 {
                    v_k_6949_ = crate::leanh::lean_ctor_get(v_p_u2081_6947_, 0);
                    crate::leanh::lean_inc(v_k_6949_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6947_, 1);
                    crate::leanh::lean_inc(v_c_6946_);
                    v___x_6950_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6949_, v_p_u2082_6945_, v_c_6946_);
                    crate::leanh::lean_dec(v_k_6949_);
                    v___x_6951_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_acc_6948_, v___x_6950_, v_c_6946_);
                    return v___x_6951_;
                } else {
                    v_k_6952_ = crate::leanh::lean_ctor_get(v_p_u2081_6947_, 0);
                    crate::leanh::lean_inc(v_k_6952_);
                    v_v_6953_ = crate::leanh::lean_ctor_get(v_p_u2081_6947_, 1);
                    crate::leanh::lean_inc(v_v_6953_);
                    v_p_6954_ = crate::leanh::lean_ctor_get(v_p_u2081_6947_, 2);
                    crate::leanh::lean_inc_ref(v_p_6954_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_6947_, 3);
                    crate::leanh::lean_inc_n(v_c_6946_, 2);
                    crate::leanh::lean_inc_ref(v_p_u2082_6945_);
                    v___x_6955_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(
                        v_k_6952_,
                        v_v_6953_,
                        v_p_u2082_6945_,
                        v_c_6946_,
                    );
                    crate::leanh::lean_dec(v_k_6952_);
                    v___x_6956_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_acc_6948_, v___x_6955_, v_c_6946_);
                    v_p_u2081_6947_ = v_p_6954_;
                    v_acc_6948_ = v___x_6956_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulC__nc(
    mut v_p_u2081_6958_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_6959_: *mut crate::leanh::LeanObject,
    mut v_c_6960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6961_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6962_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(
        v_p_u2082_6959_,
        v_c_6960_,
        v_p_u2081_6958_,
        v___x_6961_,
    );
    return v___x_6962_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC(
    mut v_p_6963_: *mut crate::leanh::LeanObject,
    mut v_k_6964_: *mut crate::leanh::LeanObject,
    mut v_c_6965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6967_: u8 = 0;
    v_zero_6966_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6967_ = lean_nat_dec_eq(v_k_6964_, v_zero_6966_);
    if v_isZero_6967_ == 1 {
        let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_c_6965_);
        crate::leanh::lean_dec_ref(v_p_6963_);
        v___x_6968_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6968_;
    } else {
        let mut v_one_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6971_: u8 = 0;
        v_one_6969_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6970_ = lean_nat_sub(v_k_6964_, v_one_6969_);
        v___x_6971_ = lean_nat_dec_eq(v_n_6970_, v_zero_6966_);
        if v___x_6971_ == 0 {
            let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_c_6965_);
            crate::leanh::lean_inc_ref(v_p_6963_);
            v___x_6972_ = l_Lean_Grind_CommRing_Poly_powC(v_p_6963_, v_n_6970_, v_c_6965_);
            crate::leanh::lean_dec(v_n_6970_);
            v___x_6973_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_6963_, v___x_6972_, v_c_6965_);
            return v___x_6973_;
        } else {
            crate::leanh::lean_dec(v_n_6970_);
            crate::leanh::lean_dec(v_c_6965_);
            return v_p_6963_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC___boxed(
    mut v_p_6974_: *mut crate::leanh::LeanObject,
    mut v_k_6975_: *mut crate::leanh::LeanObject,
    mut v_c_6976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6977_ = l_Lean_Grind_CommRing_Poly_powC(v_p_6974_, v_k_6975_, v_c_6976_);
    crate::leanh::lean_dec(v_k_6975_);
    return v_res_6977_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC__nc(
    mut v_p_6978_: *mut crate::leanh::LeanObject,
    mut v_k_6979_: *mut crate::leanh::LeanObject,
    mut v_c_6980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6982_: u8 = 0;
    v_zero_6981_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6982_ = lean_nat_dec_eq(v_k_6979_, v_zero_6981_);
    if v_isZero_6982_ == 1 {
        let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_c_6980_);
        crate::leanh::lean_dec_ref(v_p_6978_);
        v___x_6983_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6983_;
    } else {
        let mut v_one_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6986_: u8 = 0;
        v_one_6984_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6985_ = lean_nat_sub(v_k_6979_, v_one_6984_);
        v___x_6986_ = lean_nat_dec_eq(v_n_6985_, v_zero_6981_);
        if v___x_6986_ == 0 {
            let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_c_6980_);
            crate::leanh::lean_inc_ref(v_p_6978_);
            v___x_6987_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_6978_, v_n_6985_, v_c_6980_);
            crate::leanh::lean_dec(v_n_6985_);
            v___x_6988_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_6987_, v_p_6978_, v_c_6980_);
            return v___x_6988_;
        } else {
            crate::leanh::lean_dec(v_n_6985_);
            crate::leanh::lean_dec(v_c_6980_);
            return v_p_6978_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC__nc___boxed(
    mut v_p_6989_: *mut crate::leanh::LeanObject,
    mut v_k_6990_: *mut crate::leanh::LeanObject,
    mut v_c_6991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6992_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_6989_, v_k_6990_, v_c_6991_);
    crate::leanh::lean_dec(v_k_6990_);
    return v_res_6992_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC_go(
    mut v_c_6993_: *mut crate::leanh::LeanObject,
    mut v_a_6994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v_i_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7038_: u8 = 0;
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: u8 = 0;
    let mut v_k_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7044_: u8 = 0;
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7051_: u8 = 0;
    let mut v_i_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v_k_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_6994_) {
                1 => {
                    v_k_7000_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    v_isSharedCheck_7010_ = (!crate::leanh::lean_is_exclusive(v_a_6994_)) as u8;
                    if v_isSharedCheck_7010_ == 0 {
                        v___x_7002_ = v_a_6994_;
                        v_isShared_7003_ = v_isSharedCheck_7010_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_7000_);
                        crate::leanh::lean_dec(v_a_6994_);
                        v___x_7002_ = crate::leanh::lean_box(0);
                        v_isShared_7003_ = v_isSharedCheck_7010_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    crate::leanh::lean_dec(v_c_6993_);
                    v_i_7011_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    crate::leanh::lean_inc(v_i_7011_);
                    crate::leanh::lean_dec_ref_known(v_a_6994_, 1);
                    v___x_7012_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_7011_);
                    return v___x_7012_;
                }
                4 => {
                    v_a_7013_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    crate::leanh::lean_inc_ref(v_a_7013_);
                    crate::leanh::lean_dec_ref_known(v_a_6994_, 1);
                    v___x_7014_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    crate::leanh::lean_inc(v_c_6993_);
                    v___x_7015_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7013_);
                    v___x_7016_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v___x_7014_, v___x_7015_, v_c_6993_);
                    return v___x_7016_;
                }
                5 => {
                    v_a_7017_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    crate::leanh::lean_inc_ref(v_a_7017_);
                    v_b_7018_ = crate::leanh::lean_ctor_get(v_a_6994_, 1);
                    crate::leanh::lean_inc_ref(v_b_7018_);
                    crate::leanh::lean_dec_ref_known(v_a_6994_, 2);
                    crate::leanh::lean_inc_n(v_c_6993_, 2);
                    v___x_7019_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7017_);
                    v___x_7020_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_b_7018_);
                    v___x_7021_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v___x_7019_, v___x_7020_, v_c_6993_);
                    return v___x_7021_;
                }
                6 => {
                    v_a_7022_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    crate::leanh::lean_inc_ref(v_a_7022_);
                    v_b_7023_ = crate::leanh::lean_ctor_get(v_a_6994_, 1);
                    crate::leanh::lean_inc_ref(v_b_7023_);
                    crate::leanh::lean_dec_ref_known(v_a_6994_, 2);
                    crate::leanh::lean_inc_n(v_c_6993_, 3);
                    v___x_7024_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7022_);
                    v___x_7025_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_7026_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_b_7023_);
                    v___x_7027_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v___x_7025_, v___x_7026_, v_c_6993_);
                    v___x_7028_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v___x_7024_, v___x_7027_, v_c_6993_);
                    return v___x_7028_;
                }
                7 => {
                    v_a_7029_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    crate::leanh::lean_inc_ref(v_a_7029_);
                    v_b_7030_ = crate::leanh::lean_ctor_get(v_a_6994_, 1);
                    crate::leanh::lean_inc_ref(v_b_7030_);
                    crate::leanh::lean_dec_ref_known(v_a_6994_, 2);
                    crate::leanh::lean_inc_n(v_c_6993_, 2);
                    v___x_7031_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7029_);
                    v___x_7032_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_b_7030_);
                    v___x_7033_ =
                        l_Lean_Grind_CommRing_Poly_mulC(v___x_7031_, v___x_7032_, v_c_6993_);
                    return v___x_7033_;
                }
                8 => {
                    v_a_7034_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    v_k_7035_ = crate::leanh::lean_ctor_get(v_a_6994_, 1);
                    v_isSharedCheck_7062_ = (!crate::leanh::lean_is_exclusive(v_a_6994_)) as u8;
                    if v_isSharedCheck_7062_ == 0 {
                        v___x_7037_ = v_a_6994_;
                        v_isShared_7038_ = v_isSharedCheck_7062_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_7035_);
                        crate::leanh::lean_inc(v_a_7034_);
                        crate::leanh::lean_dec(v_a_6994_);
                        v___x_7037_ = crate::leanh::lean_box(0);
                        v_isShared_7038_ = v_isSharedCheck_7062_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_k_7063_ = crate::leanh::lean_ctor_get(v_a_6994_, 0);
                    crate::leanh::lean_inc(v_k_7063_);
                    crate::leanh::lean_dec_ref(v_a_6994_);
                    v_k_6996_ = v_k_7063_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_6997_ = lean_nat_to_int(v_c_6993_);
                v___x_6998_ = lean_int_emod(v_k_6996_, v___x_6997_);
                crate::leanh::lean_dec(v___x_6997_);
                crate::leanh::lean_dec(v_k_6996_);
                v___x_6999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6999_, 0, v___x_6998_);
                return v___x_6999_;
            }
            2 => {
                v___x_7004_ = lean_nat_to_int(v_k_7000_);
                v___x_7005_ = lean_nat_to_int(v_c_6993_);
                v___x_7006_ = lean_int_emod(v___x_7004_, v___x_7005_);
                crate::leanh::lean_dec(v___x_7005_);
                crate::leanh::lean_dec(v___x_7004_);
                if v_isShared_7003_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7002_, 0);
                    crate::leanh::lean_ctor_set(v___x_7002_, 0, v___x_7006_);
                    v___x_7008_ = v___x_7002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7009_, 0, v___x_7006_);
                    v___x_7008_ = v_reuseFailAlloc_7009_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7008_;
            }
            4 => {
                v___x_7039_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7040_ = lean_nat_dec_eq(v_k_7035_, v___x_7039_);
                if v___x_7040_ == 0 {
                    match crate::leanh::lean_obj_tag(v_a_7034_) {
                        0 => {
                            crate::leanh::lean_del_object(v___x_7037_);
                            v_k_7041_ = crate::leanh::lean_ctor_get(v_a_7034_, 0);
                            v_isSharedCheck_7051_ =
                                (!crate::leanh::lean_is_exclusive(v_a_7034_)) as u8;
                            if v_isSharedCheck_7051_ == 0 {
                                v___x_7043_ = v_a_7034_;
                                v_isShared_7044_ = v_isSharedCheck_7051_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_7041_);
                                crate::leanh::lean_dec(v_a_7034_);
                                v___x_7043_ = crate::leanh::lean_box(0);
                                v_isShared_7044_ = v_isSharedCheck_7051_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            crate::leanh::lean_dec(v_c_6993_);
                            v_i_7052_ = crate::leanh::lean_ctor_get(v_a_7034_, 0);
                            crate::leanh::lean_inc(v_i_7052_);
                            crate::leanh::lean_dec_ref_known(v_a_7034_, 1);
                            if v_isShared_7038_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_7037_, 0);
                                crate::leanh::lean_ctor_set(v___x_7037_, 0, v_i_7052_);
                                v___x_7054_ = v___x_7037_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_7058_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_i_7052_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 1, v_k_7035_);
                                v___x_7054_ = v_reuseFailAlloc_7058_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_del_object(v___x_7037_);
                            crate::leanh::lean_inc(v_c_6993_);
                            v___x_7059_ =
                                l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7034_);
                            v___x_7060_ =
                                l_Lean_Grind_CommRing_Poly_powC(v___x_7059_, v_k_7035_, v_c_6993_);
                            crate::leanh::lean_dec(v_k_7035_);
                            return v___x_7060_;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7037_);
                    crate::leanh::lean_dec(v_k_7035_);
                    crate::leanh::lean_dec_ref(v_a_7034_);
                    crate::leanh::lean_dec(v_c_6993_);
                    v___x_7061_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_7061_;
                }
            }
            5 => {
                v___x_7045_ = l_Int_pow(v_k_7041_, v_k_7035_);
                crate::leanh::lean_dec(v_k_7035_);
                crate::leanh::lean_dec(v_k_7041_);
                v___x_7046_ = lean_nat_to_int(v_c_6993_);
                v___x_7047_ = lean_int_emod(v___x_7045_, v___x_7046_);
                crate::leanh::lean_dec(v___x_7046_);
                crate::leanh::lean_dec(v___x_7045_);
                if v_isShared_7044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7043_, 0, v___x_7047_);
                    v___x_7049_ = v___x_7043_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7050_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_7047_);
                    v___x_7049_ = v_reuseFailAlloc_7050_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7049_;
            }
            7 => {
                v___x_7055_ = crate::leanh::lean_box(0);
                v___x_7056_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7056_, 0, v___x_7054_);
                crate::leanh::lean_ctor_set(v___x_7056_, 1, v___x_7055_);
                v___x_7057_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_7056_);
                return v___x_7057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC(
    mut v_e_7064_: *mut crate::leanh::LeanObject,
    mut v_c_7065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7066_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_7065_, v_e_7064_);
    return v___x_7066_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(
    mut v_c_7067_: *mut crate::leanh::LeanObject,
    mut v_a_7068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7077_: u8 = 0;
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7084_: u8 = 0;
    let mut v_i_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7112_: u8 = 0;
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: u8 = 0;
    let mut v_k_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7118_: u8 = 0;
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7125_: u8 = 0;
    let mut v_i_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7136_: u8 = 0;
    let mut v_k_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_7068_) {
                1 => {
                    v_k_7074_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    v_isSharedCheck_7084_ = (!crate::leanh::lean_is_exclusive(v_a_7068_)) as u8;
                    if v_isSharedCheck_7084_ == 0 {
                        v___x_7076_ = v_a_7068_;
                        v_isShared_7077_ = v_isSharedCheck_7084_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_7074_);
                        crate::leanh::lean_dec(v_a_7068_);
                        v___x_7076_ = crate::leanh::lean_box(0);
                        v_isShared_7077_ = v_isSharedCheck_7084_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    crate::leanh::lean_dec(v_c_7067_);
                    v_i_7085_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    crate::leanh::lean_inc(v_i_7085_);
                    crate::leanh::lean_dec_ref_known(v_a_7068_, 1);
                    v___x_7086_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_7085_);
                    return v___x_7086_;
                }
                4 => {
                    v_a_7087_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    crate::leanh::lean_inc_ref(v_a_7087_);
                    crate::leanh::lean_dec_ref_known(v_a_7068_, 1);
                    v___x_7088_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    crate::leanh::lean_inc(v_c_7067_);
                    v___x_7089_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7087_);
                    v___x_7090_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v___x_7088_, v___x_7089_, v_c_7067_);
                    return v___x_7090_;
                }
                5 => {
                    v_a_7091_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    crate::leanh::lean_inc_ref(v_a_7091_);
                    v_b_7092_ = crate::leanh::lean_ctor_get(v_a_7068_, 1);
                    crate::leanh::lean_inc_ref(v_b_7092_);
                    crate::leanh::lean_dec_ref_known(v_a_7068_, 2);
                    crate::leanh::lean_inc_n(v_c_7067_, 2);
                    v___x_7093_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7091_);
                    v___x_7094_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_b_7092_);
                    v___x_7095_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v___x_7093_, v___x_7094_, v_c_7067_);
                    return v___x_7095_;
                }
                6 => {
                    v_a_7096_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    crate::leanh::lean_inc_ref(v_a_7096_);
                    v_b_7097_ = crate::leanh::lean_ctor_get(v_a_7068_, 1);
                    crate::leanh::lean_inc_ref(v_b_7097_);
                    crate::leanh::lean_dec_ref_known(v_a_7068_, 2);
                    crate::leanh::lean_inc_n(v_c_7067_, 3);
                    v___x_7098_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7096_);
                    v___x_7099_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_7100_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_b_7097_);
                    v___x_7101_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v___x_7099_, v___x_7100_, v_c_7067_);
                    v___x_7102_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v___x_7098_, v___x_7101_, v_c_7067_);
                    return v___x_7102_;
                }
                7 => {
                    v_a_7103_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    crate::leanh::lean_inc_ref(v_a_7103_);
                    v_b_7104_ = crate::leanh::lean_ctor_get(v_a_7068_, 1);
                    crate::leanh::lean_inc_ref(v_b_7104_);
                    crate::leanh::lean_dec_ref_known(v_a_7068_, 2);
                    crate::leanh::lean_inc_n(v_c_7067_, 2);
                    v___x_7105_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7103_);
                    v___x_7106_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_b_7104_);
                    v___x_7107_ =
                        l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_7105_, v___x_7106_, v_c_7067_);
                    return v___x_7107_;
                }
                8 => {
                    v_a_7108_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    v_k_7109_ = crate::leanh::lean_ctor_get(v_a_7068_, 1);
                    v_isSharedCheck_7136_ = (!crate::leanh::lean_is_exclusive(v_a_7068_)) as u8;
                    if v_isSharedCheck_7136_ == 0 {
                        v___x_7111_ = v_a_7068_;
                        v_isShared_7112_ = v_isSharedCheck_7136_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_7109_);
                        crate::leanh::lean_inc(v_a_7108_);
                        crate::leanh::lean_dec(v_a_7068_);
                        v___x_7111_ = crate::leanh::lean_box(0);
                        v_isShared_7112_ = v_isSharedCheck_7136_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_k_7137_ = crate::leanh::lean_ctor_get(v_a_7068_, 0);
                    crate::leanh::lean_inc(v_k_7137_);
                    crate::leanh::lean_dec_ref(v_a_7068_);
                    v_k_7070_ = v_k_7137_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_7071_ = lean_nat_to_int(v_c_7067_);
                v___x_7072_ = lean_int_emod(v_k_7070_, v___x_7071_);
                crate::leanh::lean_dec(v___x_7071_);
                crate::leanh::lean_dec(v_k_7070_);
                v___x_7073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7073_, 0, v___x_7072_);
                return v___x_7073_;
            }
            2 => {
                v___x_7078_ = lean_nat_to_int(v_k_7074_);
                v___x_7079_ = lean_nat_to_int(v_c_7067_);
                v___x_7080_ = lean_int_emod(v___x_7078_, v___x_7079_);
                crate::leanh::lean_dec(v___x_7079_);
                crate::leanh::lean_dec(v___x_7078_);
                if v_isShared_7077_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7076_, 0);
                    crate::leanh::lean_ctor_set(v___x_7076_, 0, v___x_7080_);
                    v___x_7082_ = v___x_7076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7083_, 0, v___x_7080_);
                    v___x_7082_ = v_reuseFailAlloc_7083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7082_;
            }
            4 => {
                v___x_7113_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7114_ = lean_nat_dec_eq(v_k_7109_, v___x_7113_);
                if v___x_7114_ == 0 {
                    match crate::leanh::lean_obj_tag(v_a_7108_) {
                        0 => {
                            crate::leanh::lean_del_object(v___x_7111_);
                            v_k_7115_ = crate::leanh::lean_ctor_get(v_a_7108_, 0);
                            v_isSharedCheck_7125_ =
                                (!crate::leanh::lean_is_exclusive(v_a_7108_)) as u8;
                            if v_isSharedCheck_7125_ == 0 {
                                v___x_7117_ = v_a_7108_;
                                v_isShared_7118_ = v_isSharedCheck_7125_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_7115_);
                                crate::leanh::lean_dec(v_a_7108_);
                                v___x_7117_ = crate::leanh::lean_box(0);
                                v_isShared_7118_ = v_isSharedCheck_7125_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            crate::leanh::lean_dec(v_c_7067_);
                            v_i_7126_ = crate::leanh::lean_ctor_get(v_a_7108_, 0);
                            crate::leanh::lean_inc(v_i_7126_);
                            crate::leanh::lean_dec_ref_known(v_a_7108_, 1);
                            if v_isShared_7112_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_7111_, 0);
                                crate::leanh::lean_ctor_set(v___x_7111_, 0, v_i_7126_);
                                v___x_7128_ = v___x_7111_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_7132_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7132_, 0, v_i_7126_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7132_, 1, v_k_7109_);
                                v___x_7128_ = v_reuseFailAlloc_7132_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_del_object(v___x_7111_);
                            crate::leanh::lean_inc(v_c_7067_);
                            v___x_7133_ =
                                l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7108_);
                            v___x_7134_ = l_Lean_Grind_CommRing_Poly_powC__nc(
                                v___x_7133_,
                                v_k_7109_,
                                v_c_7067_,
                            );
                            crate::leanh::lean_dec(v_k_7109_);
                            return v___x_7134_;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7111_);
                    crate::leanh::lean_dec(v_k_7109_);
                    crate::leanh::lean_dec_ref(v_a_7108_);
                    crate::leanh::lean_dec(v_c_7067_);
                    v___x_7135_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_7135_;
                }
            }
            5 => {
                v___x_7119_ = l_Int_pow(v_k_7115_, v_k_7109_);
                crate::leanh::lean_dec(v_k_7109_);
                crate::leanh::lean_dec(v_k_7115_);
                v___x_7120_ = lean_nat_to_int(v_c_7067_);
                v___x_7121_ = lean_int_emod(v___x_7119_, v___x_7120_);
                crate::leanh::lean_dec(v___x_7120_);
                crate::leanh::lean_dec(v___x_7119_);
                if v_isShared_7118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7117_, 0, v___x_7121_);
                    v___x_7123_ = v___x_7117_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7124_, 0, v___x_7121_);
                    v___x_7123_ = v_reuseFailAlloc_7124_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7123_;
            }
            7 => {
                v___x_7129_ = crate::leanh::lean_box(0);
                v___x_7130_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7130_, 0, v___x_7128_);
                crate::leanh::lean_ctor_set(v___x_7130_, 1, v___x_7129_);
                v___x_7131_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_7130_);
                return v___x_7131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC__nc(
    mut v_e_7138_: *mut crate::leanh::LeanObject,
    mut v_c_7139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7140_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7139_, v_e_7138_);
    return v___x_7140_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(
    mut v_x_7141_: *mut crate::leanh::LeanObject,
    mut v_h__1_7142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7143_ = crate::leanh::lean_ctor_get(v_x_7141_, 0);
    crate::leanh::lean_inc(v_x_7143_);
    v_k_7144_ = crate::leanh::lean_ctor_get(v_x_7141_, 1);
    crate::leanh::lean_inc(v_k_7144_);
    crate::leanh::lean_dec_ref(v_x_7141_);
    v___x_7145_ = crate::leanh::lean_apply_2(v_h__1_7142_, v_x_7143_, v_k_7144_);
    return v___x_7145_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(
    mut v_motive_7146_: *mut crate::leanh::LeanObject,
    mut v_x_7147_: *mut crate::leanh::LeanObject,
    mut v_h__1_7148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7149_ = crate::leanh::lean_ctor_get(v_x_7147_, 0);
    crate::leanh::lean_inc(v_x_7149_);
    v_k_7150_ = crate::leanh::lean_ctor_get(v_x_7147_, 1);
    crate::leanh::lean_inc(v_k_7150_);
    crate::leanh::lean_dec_ref(v_x_7147_);
    v___x_7151_ = crate::leanh::lean_apply_2(v_h__1_7148_, v_x_7149_, v_k_7150_);
    return v___x_7151_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(
    mut v_k_7152_: *mut crate::leanh::LeanObject,
    mut v_h__1_7153_: *mut crate::leanh::LeanObject,
    mut v_h__2_7154_: *mut crate::leanh::LeanObject,
    mut v_h__3_7155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: u8 = 0;
    v___x_7156_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7157_ = lean_nat_dec_eq(v_k_7152_, v___x_7156_);
    if v___x_7157_ == 0 {
        let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7159_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_7153_);
        v___x_7158_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_7159_ = lean_nat_dec_eq(v_k_7152_, v___x_7158_);
        if v___x_7159_ == 0 {
            let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_7154_);
            v___x_7160_ = crate::leanh::lean_apply_3(
                v_h__3_7155_,
                v_k_7152_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_7160_;
        } else {
            let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7155_);
            crate::leanh::lean_dec(v_k_7152_);
            v___x_7161_ = crate::leanh::lean_box(0);
            v___x_7162_ = crate::leanh::lean_apply_1(v_h__2_7154_, v___x_7161_);
            return v___x_7162_;
        }
    } else {
        let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7155_);
        crate::leanh::lean_dec(v_h__2_7154_);
        crate::leanh::lean_dec(v_k_7152_);
        v___x_7163_ = crate::leanh::lean_box(0);
        v___x_7164_ = crate::leanh::lean_apply_1(v_h__1_7153_, v___x_7163_);
        return v___x_7164_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(
    mut v_motive_7165_: *mut crate::leanh::LeanObject,
    mut v_k_7166_: *mut crate::leanh::LeanObject,
    mut v_h__1_7167_: *mut crate::leanh::LeanObject,
    mut v_h__2_7168_: *mut crate::leanh::LeanObject,
    mut v_h__3_7169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    v___x_7170_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7171_ = lean_nat_dec_eq(v_k_7166_, v___x_7170_);
    if v___x_7171_ == 0 {
        let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7173_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_7167_);
        v___x_7172_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_7173_ = lean_nat_dec_eq(v_k_7166_, v___x_7172_);
        if v___x_7173_ == 0 {
            let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_7168_);
            v___x_7174_ = crate::leanh::lean_apply_3(
                v_h__3_7169_,
                v_k_7166_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_7174_;
        } else {
            let mut v___x_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7169_);
            crate::leanh::lean_dec(v_k_7166_);
            v___x_7175_ = crate::leanh::lean_box(0);
            v___x_7176_ = crate::leanh::lean_apply_1(v_h__2_7168_, v___x_7175_);
            return v___x_7176_;
        }
    } else {
        let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7169_);
        crate::leanh::lean_dec(v_h__2_7168_);
        crate::leanh::lean_dec(v_k_7166_);
        v___x_7177_ = crate::leanh::lean_box(0);
        v___x_7178_ = crate::leanh::lean_apply_1(v_h__1_7167_, v___x_7177_);
        return v___x_7178_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(
    mut v_m_u2081_7179_: *mut crate::leanh::LeanObject,
    mut v_h__1_7180_: *mut crate::leanh::LeanObject,
    mut v_h__2_7181_: *mut crate::leanh::LeanObject,
    mut v_h__3_7182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2081_7179_) == 0 {
        let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7182_);
        crate::leanh::lean_dec(v_h__2_7181_);
        v___x_7183_ = crate::leanh::lean_box(0);
        v___x_7184_ = crate::leanh::lean_apply_1(v_h__1_7180_, v___x_7183_);
        return v___x_7184_;
    } else {
        let mut v_m_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7180_);
        v_m_7185_ = crate::leanh::lean_ctor_get(v_m_u2081_7179_, 1);
        if crate::leanh::lean_obj_tag(v_m_7185_) == 0 {
            let mut v_p_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7182_);
            v_p_7186_ = crate::leanh::lean_ctor_get(v_m_u2081_7179_, 0);
            crate::leanh::lean_inc_ref(v_p_7186_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_7179_, 2);
            v___x_7187_ = crate::leanh::lean_apply_1(v_h__2_7181_, v_p_7186_);
            return v___x_7187_;
        } else {
            let mut v_p_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_m_7185_);
            crate::leanh::lean_dec(v_h__2_7181_);
            v_p_7188_ = crate::leanh::lean_ctor_get(v_m_u2081_7179_, 0);
            crate::leanh::lean_inc_ref(v_p_7188_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_7179_, 2);
            v___x_7189_ = crate::leanh::lean_apply_3(
                v_h__3_7182_,
                v_p_7188_,
                v_m_7185_,
                crate::leanh::lean_box(0),
            );
            return v___x_7189_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(
    mut v_motive_7190_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_7191_: *mut crate::leanh::LeanObject,
    mut v_h__1_7192_: *mut crate::leanh::LeanObject,
    mut v_h__2_7193_: *mut crate::leanh::LeanObject,
    mut v_h__3_7194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2081_7191_) == 0 {
        let mut v___x_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7194_);
        crate::leanh::lean_dec(v_h__2_7193_);
        v___x_7195_ = crate::leanh::lean_box(0);
        v___x_7196_ = crate::leanh::lean_apply_1(v_h__1_7192_, v___x_7195_);
        return v___x_7196_;
    } else {
        let mut v_m_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7192_);
        v_m_7197_ = crate::leanh::lean_ctor_get(v_m_u2081_7191_, 1);
        if crate::leanh::lean_obj_tag(v_m_7197_) == 0 {
            let mut v_p_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7194_);
            v_p_7198_ = crate::leanh::lean_ctor_get(v_m_u2081_7191_, 0);
            crate::leanh::lean_inc_ref(v_p_7198_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_7191_, 2);
            v___x_7199_ = crate::leanh::lean_apply_1(v_h__2_7193_, v_p_7198_);
            return v___x_7199_;
        } else {
            let mut v_p_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_m_7197_);
            crate::leanh::lean_dec(v_h__2_7193_);
            v_p_7200_ = crate::leanh::lean_ctor_get(v_m_u2081_7191_, 0);
            crate::leanh::lean_inc_ref(v_p_7200_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_7191_, 2);
            v___x_7201_ = crate::leanh::lean_apply_3(
                v_h__3_7194_,
                v_p_7200_,
                v_m_7197_,
                crate::leanh::lean_box(0),
            );
            return v___x_7201_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(
    mut v_a_7202_: u8,
    mut v_h__1_7203_: *mut crate::leanh::LeanObject,
    mut v_h__2_7204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_a_7202_ == 1 {
        let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7204_);
        v___x_7205_ = crate::leanh::lean_box(0);
        v___x_7206_ = crate::leanh::lean_apply_1(v_h__1_7203_, v___x_7205_);
        return v___x_7206_;
    } else {
        let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7203_);
        v___x_7207_ = crate::leanh::lean_box((v_a_7202_) as usize);
        v___x_7208_ =
            crate::leanh::lean_apply_2(v_h__2_7204_, v___x_7207_, crate::leanh::lean_box(0));
        return v___x_7208_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(
    mut v_a_7209_: *mut crate::leanh::LeanObject,
    mut v_h__1_7210_: *mut crate::leanh::LeanObject,
    mut v_h__2_7211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_17__boxed_7212_: u8 = 0;
    let mut v_res_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_17__boxed_7212_ = (crate::leanh::lean_unbox(v_a_7209_) as u8);
    v_res_7213_ =
        l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(
            v_a_17__boxed_7212_,
            v_h__1_7210_,
            v_h__2_7211_,
        );
    return v_res_7213_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(
    mut v_motive_7214_: *mut crate::leanh::LeanObject,
    mut v_a_7215_: u8,
    mut v_h__1_7216_: *mut crate::leanh::LeanObject,
    mut v_h__2_7217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_a_7215_ == 1 {
        let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7217_);
        v___x_7218_ = crate::leanh::lean_box(0);
        v___x_7219_ = crate::leanh::lean_apply_1(v_h__1_7216_, v___x_7218_);
        return v___x_7219_;
    } else {
        let mut v___x_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7216_);
        v___x_7220_ = crate::leanh::lean_box((v_a_7215_) as usize);
        v___x_7221_ =
            crate::leanh::lean_apply_2(v_h__2_7217_, v___x_7220_, crate::leanh::lean_box(0));
        return v___x_7221_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(
    mut v_motive_7222_: *mut crate::leanh::LeanObject,
    mut v_a_7223_: *mut crate::leanh::LeanObject,
    mut v_h__1_7224_: *mut crate::leanh::LeanObject,
    mut v_h__2_7225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_28__boxed_7226_: u8 = 0;
    let mut v_res_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_28__boxed_7226_ = (crate::leanh::lean_unbox(v_a_7223_) as u8);
    v_res_7227_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(
        v_motive_7222_,
        v_a_28__boxed_7226_,
        v_h__1_7224_,
        v_h__2_7225_,
    );
    return v_res_7227_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(
    mut v_p_7228_: *mut crate::leanh::LeanObject,
    mut v_h__1_7229_: *mut crate::leanh::LeanObject,
    mut v_h__2_7230_: *mut crate::leanh::LeanObject,
    mut v_h__3_7231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_7228_) == 0 {
        let mut v_k_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7234_: u8 = 0;
        crate::leanh::lean_dec(v_h__3_7231_);
        v_k_7232_ = crate::leanh::lean_ctor_get(v_p_7228_, 0);
        crate::leanh::lean_inc(v_k_7232_);
        crate::leanh::lean_dec_ref_known(v_p_7228_, 1);
        v___x_7233_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
        );
        v___x_7234_ = lean_int_dec_eq(v_k_7232_, v___x_7233_);
        if v___x_7234_ == 0 {
            let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_7229_);
            v___x_7235_ =
                crate::leanh::lean_apply_2(v_h__2_7230_, v_k_7232_, crate::leanh::lean_box(0));
            return v___x_7235_;
        } else {
            let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_7232_);
            crate::leanh::lean_dec(v_h__2_7230_);
            v___x_7236_ = crate::leanh::lean_box(0);
            v___x_7237_ = crate::leanh::lean_apply_1(v_h__1_7229_, v___x_7236_);
            return v___x_7237_;
        }
    } else {
        let mut v_k_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7230_);
        crate::leanh::lean_dec(v_h__1_7229_);
        v_k_7238_ = crate::leanh::lean_ctor_get(v_p_7228_, 0);
        crate::leanh::lean_inc(v_k_7238_);
        v_v_7239_ = crate::leanh::lean_ctor_get(v_p_7228_, 1);
        crate::leanh::lean_inc(v_v_7239_);
        v_p_7240_ = crate::leanh::lean_ctor_get(v_p_7228_, 2);
        crate::leanh::lean_inc_ref(v_p_7240_);
        crate::leanh::lean_dec_ref_known(v_p_7228_, 3);
        v___x_7241_ = crate::leanh::lean_apply_3(v_h__3_7231_, v_k_7238_, v_v_7239_, v_p_7240_);
        return v___x_7241_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(
    mut v_motive_7242_: *mut crate::leanh::LeanObject,
    mut v_p_7243_: *mut crate::leanh::LeanObject,
    mut v_h__1_7244_: *mut crate::leanh::LeanObject,
    mut v_h__2_7245_: *mut crate::leanh::LeanObject,
    mut v_h__3_7246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_7243_) == 0 {
        let mut v_k_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7249_: u8 = 0;
        crate::leanh::lean_dec(v_h__3_7246_);
        v_k_7247_ = crate::leanh::lean_ctor_get(v_p_7243_, 0);
        crate::leanh::lean_inc(v_k_7247_);
        crate::leanh::lean_dec_ref_known(v_p_7243_, 1);
        v___x_7248_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
        );
        v___x_7249_ = lean_int_dec_eq(v_k_7247_, v___x_7248_);
        if v___x_7249_ == 0 {
            let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_7244_);
            v___x_7250_ =
                crate::leanh::lean_apply_2(v_h__2_7245_, v_k_7247_, crate::leanh::lean_box(0));
            return v___x_7250_;
        } else {
            let mut v___x_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_7247_);
            crate::leanh::lean_dec(v_h__2_7245_);
            v___x_7251_ = crate::leanh::lean_box(0);
            v___x_7252_ = crate::leanh::lean_apply_1(v_h__1_7244_, v___x_7251_);
            return v___x_7252_;
        }
    } else {
        let mut v_k_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7245_);
        crate::leanh::lean_dec(v_h__1_7244_);
        v_k_7253_ = crate::leanh::lean_ctor_get(v_p_7243_, 0);
        crate::leanh::lean_inc(v_k_7253_);
        v_v_7254_ = crate::leanh::lean_ctor_get(v_p_7243_, 1);
        crate::leanh::lean_inc(v_v_7254_);
        v_p_7255_ = crate::leanh::lean_ctor_get(v_p_7243_, 2);
        crate::leanh::lean_inc_ref(v_p_7255_);
        crate::leanh::lean_dec_ref_known(v_p_7243_, 3);
        v___x_7256_ = crate::leanh::lean_apply_3(v_h__3_7246_, v_k_7253_, v_v_7254_, v_p_7255_);
        return v___x_7256_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(
    mut v_k_7257_: *mut crate::leanh::LeanObject,
    mut v_h__1_7258_: *mut crate::leanh::LeanObject,
    mut v_h__2_7259_: *mut crate::leanh::LeanObject,
    mut v_h__3_7260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7262_: u8 = 0;
    v_zero_7261_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_7262_ = lean_nat_dec_eq(v_k_7257_, v_zero_7261_);
    if v_isZero_7262_ == 1 {
        let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7260_);
        crate::leanh::lean_dec(v_h__2_7259_);
        v___x_7263_ = crate::leanh::lean_box(0);
        v___x_7264_ = crate::leanh::lean_apply_1(v_h__1_7258_, v___x_7263_);
        return v___x_7264_;
    } else {
        let mut v_one_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7267_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_7258_);
        v_one_7265_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_7266_ = lean_nat_sub(v_k_7257_, v_one_7265_);
        v___x_7267_ = lean_nat_dec_eq(v_n_7266_, v_zero_7261_);
        if v___x_7267_ == 0 {
            let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_7259_);
            v___x_7268_ =
                crate::leanh::lean_apply_2(v_h__3_7260_, v_n_7266_, crate::leanh::lean_box(0));
            return v___x_7268_;
        } else {
            let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_n_7266_);
            crate::leanh::lean_dec(v_h__3_7260_);
            v___x_7269_ = crate::leanh::lean_box(0);
            v___x_7270_ = crate::leanh::lean_apply_1(v_h__2_7259_, v___x_7269_);
            return v___x_7270_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(
    mut v_k_7271_: *mut crate::leanh::LeanObject,
    mut v_h__1_7272_: *mut crate::leanh::LeanObject,
    mut v_h__2_7273_: *mut crate::leanh::LeanObject,
    mut v_h__3_7274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7275_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_7271_, v_h__1_7272_, v_h__2_7273_, v_h__3_7274_);
    crate::leanh::lean_dec(v_k_7271_);
    return v_res_7275_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(
    mut v_motive_7276_: *mut crate::leanh::LeanObject,
    mut v_k_7277_: *mut crate::leanh::LeanObject,
    mut v_h__1_7278_: *mut crate::leanh::LeanObject,
    mut v_h__2_7279_: *mut crate::leanh::LeanObject,
    mut v_h__3_7280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7282_: u8 = 0;
    v_zero_7281_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_7282_ = lean_nat_dec_eq(v_k_7277_, v_zero_7281_);
    if v_isZero_7282_ == 1 {
        let mut v___x_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7280_);
        crate::leanh::lean_dec(v_h__2_7279_);
        v___x_7283_ = crate::leanh::lean_box(0);
        v___x_7284_ = crate::leanh::lean_apply_1(v_h__1_7278_, v___x_7283_);
        return v___x_7284_;
    } else {
        let mut v_one_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7287_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_7278_);
        v_one_7285_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_7286_ = lean_nat_sub(v_k_7277_, v_one_7285_);
        v___x_7287_ = lean_nat_dec_eq(v_n_7286_, v_zero_7281_);
        if v___x_7287_ == 0 {
            let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_7279_);
            v___x_7288_ =
                crate::leanh::lean_apply_2(v_h__3_7280_, v_n_7286_, crate::leanh::lean_box(0));
            return v___x_7288_;
        } else {
            let mut v___x_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_n_7286_);
            crate::leanh::lean_dec(v_h__3_7280_);
            v___x_7289_ = crate::leanh::lean_box(0);
            v___x_7290_ = crate::leanh::lean_apply_1(v_h__2_7279_, v___x_7289_);
            return v___x_7290_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(
    mut v_motive_7291_: *mut crate::leanh::LeanObject,
    mut v_k_7292_: *mut crate::leanh::LeanObject,
    mut v_h__1_7293_: *mut crate::leanh::LeanObject,
    mut v_h__2_7294_: *mut crate::leanh::LeanObject,
    mut v_h__3_7295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7296_ =
        l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(
            v_motive_7291_,
            v_k_7292_,
            v_h__1_7293_,
            v_h__2_7294_,
            v_h__3_7295_,
        );
    crate::leanh::lean_dec(v_k_7292_);
    return v_res_7296_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(
    mut v_x_7297_: *mut crate::leanh::LeanObject,
    mut v_h__1_7298_: *mut crate::leanh::LeanObject,
    mut v_h__2_7299_: *mut crate::leanh::LeanObject,
    mut v_h__3_7300_: *mut crate::leanh::LeanObject,
    mut v_h__4_7301_: *mut crate::leanh::LeanObject,
    mut v_h__5_7302_: *mut crate::leanh::LeanObject,
    mut v_h__6_7303_: *mut crate::leanh::LeanObject,
    mut v_h__7_7304_: *mut crate::leanh::LeanObject,
    mut v_h__8_7305_: *mut crate::leanh::LeanObject,
    mut v_h__9_7306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_7297_) {
        0 => {
            let mut v_k_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            v_k_7307_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc(v_k_7307_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 1);
            v___x_7308_ = crate::leanh::lean_apply_1(v_h__1_7298_, v_k_7307_);
            return v___x_7308_;
        }
        1 => {
            let mut v_k_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_k_7309_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc(v_k_7309_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 1);
            v___x_7310_ = crate::leanh::lean_apply_1(v_h__2_7299_, v_k_7309_);
            return v___x_7310_;
        }
        2 => {
            let mut v_k_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_k_7311_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc(v_k_7311_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 1);
            v___x_7312_ = crate::leanh::lean_apply_1(v_h__3_7300_, v_k_7311_);
            return v___x_7312_;
        }
        3 => {
            let mut v_i_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_i_7313_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc(v_i_7313_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 1);
            v___x_7314_ = crate::leanh::lean_apply_1(v_h__4_7301_, v_i_7313_);
            return v___x_7314_;
        }
        4 => {
            let mut v_a_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_a_7315_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc_ref(v_a_7315_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 1);
            v___x_7316_ = crate::leanh::lean_apply_1(v_h__7_7304_, v_a_7315_);
            return v___x_7316_;
        }
        5 => {
            let mut v_a_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_a_7317_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc_ref(v_a_7317_);
            v_b_7318_ = crate::leanh::lean_ctor_get(v_x_7297_, 1);
            crate::leanh::lean_inc_ref(v_b_7318_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 2);
            v___x_7319_ = crate::leanh::lean_apply_2(v_h__5_7302_, v_a_7317_, v_b_7318_);
            return v___x_7319_;
        }
        6 => {
            let mut v_a_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_a_7320_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc_ref(v_a_7320_);
            v_b_7321_ = crate::leanh::lean_ctor_get(v_x_7297_, 1);
            crate::leanh::lean_inc_ref(v_b_7321_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 2);
            v___x_7322_ = crate::leanh::lean_apply_2(v_h__8_7305_, v_a_7320_, v_b_7321_);
            return v___x_7322_;
        }
        7 => {
            let mut v_a_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7306_);
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_a_7323_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc_ref(v_a_7323_);
            v_b_7324_ = crate::leanh::lean_ctor_get(v_x_7297_, 1);
            crate::leanh::lean_inc_ref(v_b_7324_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 2);
            v___x_7325_ = crate::leanh::lean_apply_2(v_h__6_7303_, v_a_7323_, v_b_7324_);
            return v___x_7325_;
        }
        _ => {
            let mut v_a_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_7305_);
            crate::leanh::lean_dec(v_h__7_7304_);
            crate::leanh::lean_dec(v_h__6_7303_);
            crate::leanh::lean_dec(v_h__5_7302_);
            crate::leanh::lean_dec(v_h__4_7301_);
            crate::leanh::lean_dec(v_h__3_7300_);
            crate::leanh::lean_dec(v_h__2_7299_);
            crate::leanh::lean_dec(v_h__1_7298_);
            v_a_7326_ = crate::leanh::lean_ctor_get(v_x_7297_, 0);
            crate::leanh::lean_inc_ref(v_a_7326_);
            v_k_7327_ = crate::leanh::lean_ctor_get(v_x_7297_, 1);
            crate::leanh::lean_inc(v_k_7327_);
            crate::leanh::lean_dec_ref_known(v_x_7297_, 2);
            v___x_7328_ = crate::leanh::lean_apply_2(v_h__9_7306_, v_a_7326_, v_k_7327_);
            return v___x_7328_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(
    mut v_motive_7329_: *mut crate::leanh::LeanObject,
    mut v_x_7330_: *mut crate::leanh::LeanObject,
    mut v_h__1_7331_: *mut crate::leanh::LeanObject,
    mut v_h__2_7332_: *mut crate::leanh::LeanObject,
    mut v_h__3_7333_: *mut crate::leanh::LeanObject,
    mut v_h__4_7334_: *mut crate::leanh::LeanObject,
    mut v_h__5_7335_: *mut crate::leanh::LeanObject,
    mut v_h__6_7336_: *mut crate::leanh::LeanObject,
    mut v_h__7_7337_: *mut crate::leanh::LeanObject,
    mut v_h__8_7338_: *mut crate::leanh::LeanObject,
    mut v_h__9_7339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_7330_) {
        0 => {
            let mut v_k_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            v_k_7340_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc(v_k_7340_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 1);
            v___x_7341_ = crate::leanh::lean_apply_1(v_h__1_7331_, v_k_7340_);
            return v___x_7341_;
        }
        1 => {
            let mut v_k_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_k_7342_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc(v_k_7342_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 1);
            v___x_7343_ = crate::leanh::lean_apply_1(v_h__2_7332_, v_k_7342_);
            return v___x_7343_;
        }
        2 => {
            let mut v_k_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_k_7344_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc(v_k_7344_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 1);
            v___x_7345_ = crate::leanh::lean_apply_1(v_h__3_7333_, v_k_7344_);
            return v___x_7345_;
        }
        3 => {
            let mut v_i_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_i_7346_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc(v_i_7346_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 1);
            v___x_7347_ = crate::leanh::lean_apply_1(v_h__4_7334_, v_i_7346_);
            return v___x_7347_;
        }
        4 => {
            let mut v_a_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_a_7348_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc_ref(v_a_7348_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 1);
            v___x_7349_ = crate::leanh::lean_apply_1(v_h__7_7337_, v_a_7348_);
            return v___x_7349_;
        }
        5 => {
            let mut v_a_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_a_7350_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc_ref(v_a_7350_);
            v_b_7351_ = crate::leanh::lean_ctor_get(v_x_7330_, 1);
            crate::leanh::lean_inc_ref(v_b_7351_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 2);
            v___x_7352_ = crate::leanh::lean_apply_2(v_h__5_7335_, v_a_7350_, v_b_7351_);
            return v___x_7352_;
        }
        6 => {
            let mut v_a_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_a_7353_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc_ref(v_a_7353_);
            v_b_7354_ = crate::leanh::lean_ctor_get(v_x_7330_, 1);
            crate::leanh::lean_inc_ref(v_b_7354_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 2);
            v___x_7355_ = crate::leanh::lean_apply_2(v_h__8_7338_, v_a_7353_, v_b_7354_);
            return v___x_7355_;
        }
        7 => {
            let mut v_a_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_7339_);
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_a_7356_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc_ref(v_a_7356_);
            v_b_7357_ = crate::leanh::lean_ctor_get(v_x_7330_, 1);
            crate::leanh::lean_inc_ref(v_b_7357_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 2);
            v___x_7358_ = crate::leanh::lean_apply_2(v_h__6_7336_, v_a_7356_, v_b_7357_);
            return v___x_7358_;
        }
        _ => {
            let mut v_a_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_7338_);
            crate::leanh::lean_dec(v_h__7_7337_);
            crate::leanh::lean_dec(v_h__6_7336_);
            crate::leanh::lean_dec(v_h__5_7335_);
            crate::leanh::lean_dec(v_h__4_7334_);
            crate::leanh::lean_dec(v_h__3_7333_);
            crate::leanh::lean_dec(v_h__2_7332_);
            crate::leanh::lean_dec(v_h__1_7331_);
            v_a_7359_ = crate::leanh::lean_ctor_get(v_x_7330_, 0);
            crate::leanh::lean_inc_ref(v_a_7359_);
            v_k_7360_ = crate::leanh::lean_ctor_get(v_x_7330_, 1);
            crate::leanh::lean_inc(v_k_7360_);
            crate::leanh::lean_dec_ref_known(v_x_7330_, 2);
            v___x_7361_ = crate::leanh::lean_apply_2(v_h__9_7339_, v_a_7359_, v_k_7360_);
            return v___x_7361_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(
    mut v_a_7362_: *mut crate::leanh::LeanObject,
    mut v_h__1_7363_: *mut crate::leanh::LeanObject,
    mut v_h__2_7364_: *mut crate::leanh::LeanObject,
    mut v_h__3_7365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_7362_) {
        0 => {
            let mut v_k_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7365_);
            crate::leanh::lean_dec(v_h__2_7364_);
            v_k_7366_ = crate::leanh::lean_ctor_get(v_a_7362_, 0);
            crate::leanh::lean_inc(v_k_7366_);
            crate::leanh::lean_dec_ref_known(v_a_7362_, 1);
            v___x_7367_ = crate::leanh::lean_apply_1(v_h__1_7363_, v_k_7366_);
            return v___x_7367_;
        }
        3 => {
            let mut v_i_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7365_);
            crate::leanh::lean_dec(v_h__1_7363_);
            v_i_7368_ = crate::leanh::lean_ctor_get(v_a_7362_, 0);
            crate::leanh::lean_inc(v_i_7368_);
            crate::leanh::lean_dec_ref_known(v_a_7362_, 1);
            v___x_7369_ = crate::leanh::lean_apply_1(v_h__2_7364_, v_i_7368_);
            return v___x_7369_;
        }
        _ => {
            let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_7364_);
            crate::leanh::lean_dec(v_h__1_7363_);
            v___x_7370_ = crate::leanh::lean_apply_3(
                v_h__3_7365_,
                v_a_7362_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_7370_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(
    mut v_motive_7371_: *mut crate::leanh::LeanObject,
    mut v_a_7372_: *mut crate::leanh::LeanObject,
    mut v_h__1_7373_: *mut crate::leanh::LeanObject,
    mut v_h__2_7374_: *mut crate::leanh::LeanObject,
    mut v_h__3_7375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_7372_) {
        0 => {
            let mut v_k_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7375_);
            crate::leanh::lean_dec(v_h__2_7374_);
            v_k_7376_ = crate::leanh::lean_ctor_get(v_a_7372_, 0);
            crate::leanh::lean_inc(v_k_7376_);
            crate::leanh::lean_dec_ref_known(v_a_7372_, 1);
            v___x_7377_ = crate::leanh::lean_apply_1(v_h__1_7373_, v_k_7376_);
            return v___x_7377_;
        }
        3 => {
            let mut v_i_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7375_);
            crate::leanh::lean_dec(v_h__1_7373_);
            v_i_7378_ = crate::leanh::lean_ctor_get(v_a_7372_, 0);
            crate::leanh::lean_inc(v_i_7378_);
            crate::leanh::lean_dec_ref_known(v_a_7372_, 1);
            v___x_7379_ = crate::leanh::lean_apply_1(v_h__2_7374_, v_i_7378_);
            return v___x_7379_;
        }
        _ => {
            let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_7374_);
            crate::leanh::lean_dec(v_h__1_7373_);
            v___x_7380_ = crate::leanh::lean_apply_3(
                v_h__3_7375_,
                v_a_7372_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_7380_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
    mut v_inst_7381_: *mut crate::leanh::LeanObject,
    mut v_ctx_7382_: *mut crate::leanh::LeanObject,
    mut v_m_7383_: *mut crate::leanh::LeanObject,
    mut v_acc_7384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMul_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: u8 = 0;
    let mut v___x_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: u8 = 0;
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_7383_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_7381_);
                    return v_acc_7384_;
                } else {
                    v_toSemiring_7385_ = crate::leanh::lean_ctor_get(v_inst_7381_, 0);
                    v_toMul_7386_ = crate::leanh::lean_ctor_get(v_toSemiring_7385_, 1);
                    v_ofNat_7387_ = crate::leanh::lean_ctor_get(v_toSemiring_7385_, 3);
                    v_npow_7388_ = crate::leanh::lean_ctor_get(v_toSemiring_7385_, 5);
                    v_p_7389_ = crate::leanh::lean_ctor_get(v_m_7383_, 0);
                    crate::leanh::lean_inc_ref(v_p_7389_);
                    v_m_7390_ = crate::leanh::lean_ctor_get(v_m_7383_, 1);
                    crate::leanh::lean_inc(v_m_7390_);
                    crate::leanh::lean_dec_ref_known(v_m_7383_, 2);
                    v_x_7395_ = crate::leanh::lean_ctor_get(v_p_7389_, 0);
                    crate::leanh::lean_inc(v_x_7395_);
                    v_k_7396_ = crate::leanh::lean_ctor_get(v_p_7389_, 1);
                    crate::leanh::lean_inc(v_k_7396_);
                    crate::leanh::lean_dec_ref(v_p_7389_);
                    v___x_7397_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7398_ = lean_nat_dec_eq(v_k_7396_, v___x_7397_);
                    if v___x_7398_ == 0 {
                        v___x_7399_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7400_ = lean_nat_dec_eq(v_k_7396_, v___x_7399_);
                        if v___x_7400_ == 0 {
                            v___x_7401_ = l_Lean_RArray_getImpl___redArg(v_ctx_7382_, v_x_7395_);
                            crate::leanh::lean_dec(v_x_7395_);
                            crate::leanh::lean_inc(v_npow_7388_);
                            v___x_7402_ =
                                crate::leanh::lean_apply_2(v_npow_7388_, v___x_7401_, v_k_7396_);
                            v___y_7392_ = v___x_7402_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_k_7396_);
                            v___x_7403_ = l_Lean_RArray_getImpl___redArg(v_ctx_7382_, v_x_7395_);
                            crate::leanh::lean_dec(v_x_7395_);
                            v___y_7392_ = v___x_7403_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_7396_);
                        crate::leanh::lean_dec(v_x_7395_);
                        v___x_7404_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v_ofNat_7387_);
                        v___x_7405_ = crate::leanh::lean_apply_1(v_ofNat_7387_, v___x_7404_);
                        v___y_7392_ = v___x_7405_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toMul_7386_);
                v___x_7393_ = crate::leanh::lean_apply_2(v_toMul_7386_, v_acc_7384_, v___y_7392_);
                v_m_7383_ = v_m_7390_;
                v_acc_7384_ = v___x_7393_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(
    mut v_inst_7406_: *mut crate::leanh::LeanObject,
    mut v_ctx_7407_: *mut crate::leanh::LeanObject,
    mut v_m_7408_: *mut crate::leanh::LeanObject,
    mut v_acc_7409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7410_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
        v_inst_7406_,
        v_ctx_7407_,
        v_m_7408_,
        v_acc_7409_,
    );
    crate::leanh::lean_dec_ref(v_ctx_7407_);
    return v_res_7410_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(
    mut v_00_u03b1_7411_: *mut crate::leanh::LeanObject,
    mut v_inst_7412_: *mut crate::leanh::LeanObject,
    mut v_ctx_7413_: *mut crate::leanh::LeanObject,
    mut v_m_7414_: *mut crate::leanh::LeanObject,
    mut v_acc_7415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7416_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
        v_inst_7412_,
        v_ctx_7413_,
        v_m_7414_,
        v_acc_7415_,
    );
    return v___x_7416_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(
    mut v_00_u03b1_7417_: *mut crate::leanh::LeanObject,
    mut v_inst_7418_: *mut crate::leanh::LeanObject,
    mut v_ctx_7419_: *mut crate::leanh::LeanObject,
    mut v_m_7420_: *mut crate::leanh::LeanObject,
    mut v_acc_7421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7422_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(
        v_00_u03b1_7417_,
        v_inst_7418_,
        v_ctx_7419_,
        v_m_7420_,
        v_acc_7421_,
    );
    crate::leanh::lean_dec_ref(v_ctx_7419_);
    return v_res_7422_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(
    mut v_inst_7423_: *mut crate::leanh::LeanObject,
    mut v_ctx_7424_: *mut crate::leanh::LeanObject,
    mut v_m_7425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_7425_) == 0 {
        let mut v_toSemiring_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toSemiring_7426_ = crate::leanh::lean_ctor_get(v_inst_7423_, 0);
        crate::leanh::lean_inc_ref(v_toSemiring_7426_);
        crate::leanh::lean_dec_ref(v_inst_7423_);
        v_ofNat_7427_ = crate::leanh::lean_ctor_get(v_toSemiring_7426_, 3);
        crate::leanh::lean_inc(v_ofNat_7427_);
        crate::leanh::lean_dec_ref(v_toSemiring_7426_);
        v___x_7428_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_7429_ = crate::leanh::lean_apply_1(v_ofNat_7427_, v___x_7428_);
        return v___x_7429_;
    } else {
        let mut v_toSemiring_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_npow_7434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7438_: u8 = 0;
        v_toSemiring_7430_ = crate::leanh::lean_ctor_get(v_inst_7423_, 0);
        v_p_7431_ = crate::leanh::lean_ctor_get(v_m_7425_, 0);
        crate::leanh::lean_inc_ref(v_p_7431_);
        v_m_7432_ = crate::leanh::lean_ctor_get(v_m_7425_, 1);
        crate::leanh::lean_inc(v_m_7432_);
        crate::leanh::lean_dec_ref_known(v_m_7425_, 2);
        v_ofNat_7433_ = crate::leanh::lean_ctor_get(v_toSemiring_7430_, 3);
        v_npow_7434_ = crate::leanh::lean_ctor_get(v_toSemiring_7430_, 5);
        v_x_7435_ = crate::leanh::lean_ctor_get(v_p_7431_, 0);
        crate::leanh::lean_inc(v_x_7435_);
        v_k_7436_ = crate::leanh::lean_ctor_get(v_p_7431_, 1);
        crate::leanh::lean_inc(v_k_7436_);
        crate::leanh::lean_dec_ref(v_p_7431_);
        v___x_7437_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_7438_ = lean_nat_dec_eq(v_k_7436_, v___x_7437_);
        if v___x_7438_ == 0 {
            let mut v___x_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7440_: u8 = 0;
            v___x_7439_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_7440_ = lean_nat_dec_eq(v_k_7436_, v___x_7439_);
            if v___x_7440_ == 0 {
                let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_7441_ = l_Lean_RArray_getImpl___redArg(v_ctx_7424_, v_x_7435_);
                crate::leanh::lean_dec(v_x_7435_);
                crate::leanh::lean_inc(v_npow_7434_);
                v___x_7442_ = crate::leanh::lean_apply_2(v_npow_7434_, v___x_7441_, v_k_7436_);
                v___x_7443_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
                    v_inst_7423_,
                    v_ctx_7424_,
                    v_m_7432_,
                    v___x_7442_,
                );
                return v___x_7443_;
            } else {
                let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_k_7436_);
                v___x_7444_ = l_Lean_RArray_getImpl___redArg(v_ctx_7424_, v_x_7435_);
                crate::leanh::lean_dec(v_x_7435_);
                v___x_7445_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
                    v_inst_7423_,
                    v_ctx_7424_,
                    v_m_7432_,
                    v___x_7444_,
                );
                return v___x_7445_;
            }
        } else {
            let mut v___x_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_7436_);
            crate::leanh::lean_dec(v_x_7435_);
            v___x_7446_ = crate::leanh::lean_unsigned_to_nat(1);
            crate::leanh::lean_inc(v_ofNat_7433_);
            v___x_7447_ = crate::leanh::lean_apply_1(v_ofNat_7433_, v___x_7446_);
            v___x_7448_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
                v_inst_7423_,
                v_ctx_7424_,
                v_m_7432_,
                v___x_7447_,
            );
            return v___x_7448_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(
    mut v_inst_7449_: *mut crate::leanh::LeanObject,
    mut v_ctx_7450_: *mut crate::leanh::LeanObject,
    mut v_m_7451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7452_ =
        l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_7449_, v_ctx_7450_, v_m_7451_);
    crate::leanh::lean_dec_ref(v_ctx_7450_);
    return v_res_7452_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule(
    mut v_00_u03b1_7453_: *mut crate::leanh::LeanObject,
    mut v_inst_7454_: *mut crate::leanh::LeanObject,
    mut v_ctx_7455_: *mut crate::leanh::LeanObject,
    mut v_m_7456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7457_ =
        l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_7454_, v_ctx_7455_, v_m_7456_);
    return v___x_7457_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(
    mut v_00_u03b1_7458_: *mut crate::leanh::LeanObject,
    mut v_inst_7459_: *mut crate::leanh::LeanObject,
    mut v_ctx_7460_: *mut crate::leanh::LeanObject,
    mut v_m_7461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7462_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(
        v_00_u03b1_7458_,
        v_inst_7459_,
        v_ctx_7460_,
        v_m_7461_,
    );
    crate::leanh::lean_dec_ref(v_ctx_7460_);
    return v_res_7462_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(
    mut v_inst_7463_: *mut crate::leanh::LeanObject,
    mut v_ctx_7464_: *mut crate::leanh::LeanObject,
    mut v_p_7465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_7463_);
    v___x_7466_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_7463_);
    if crate::leanh::lean_obj_tag(v_p_7465_) == 0 {
        let mut v_toSemiring_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zsmul_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_7469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toSemiring_7467_ = crate::leanh::lean_ctor_get(v_inst_7463_, 0);
        crate::leanh::lean_inc_ref(v_toSemiring_7467_);
        crate::leanh::lean_dec_ref(v_inst_7463_);
        v_zsmul_7468_ = crate::leanh::lean_ctor_get(v___x_7466_, 2);
        crate::leanh::lean_inc(v_zsmul_7468_);
        crate::leanh::lean_dec_ref(v___x_7466_);
        v_ofNat_7469_ = crate::leanh::lean_ctor_get(v_toSemiring_7467_, 3);
        crate::leanh::lean_inc(v_ofNat_7469_);
        crate::leanh::lean_dec_ref(v_toSemiring_7467_);
        v_k_7470_ = crate::leanh::lean_ctor_get(v_p_7465_, 0);
        crate::leanh::lean_inc(v_k_7470_);
        crate::leanh::lean_dec_ref_known(v_p_7465_, 1);
        v___x_7471_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_7472_ = crate::leanh::lean_apply_1(v_ofNat_7469_, v___x_7471_);
        v___x_7473_ = crate::leanh::lean_apply_2(v_zsmul_7468_, v_k_7470_, v___x_7472_);
        return v___x_7473_;
    } else {
        let mut v_toSemiring_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zsmul_7475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toAdd_7476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toSemiring_7474_ = crate::leanh::lean_ctor_get(v_inst_7463_, 0);
        v_zsmul_7475_ = crate::leanh::lean_ctor_get(v___x_7466_, 2);
        crate::leanh::lean_inc(v_zsmul_7475_);
        crate::leanh::lean_dec_ref(v___x_7466_);
        v_toAdd_7476_ = crate::leanh::lean_ctor_get(v_toSemiring_7474_, 0);
        crate::leanh::lean_inc(v_toAdd_7476_);
        v_k_7477_ = crate::leanh::lean_ctor_get(v_p_7465_, 0);
        crate::leanh::lean_inc(v_k_7477_);
        v_v_7478_ = crate::leanh::lean_ctor_get(v_p_7465_, 1);
        crate::leanh::lean_inc(v_v_7478_);
        v_p_7479_ = crate::leanh::lean_ctor_get(v_p_7465_, 2);
        crate::leanh::lean_inc_ref(v_p_7479_);
        crate::leanh::lean_dec_ref_known(v_p_7465_, 3);
        crate::leanh::lean_inc_ref(v_inst_7463_);
        v___x_7480_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(
            v_inst_7463_,
            v_ctx_7464_,
            v_v_7478_,
        );
        v___x_7481_ = crate::leanh::lean_apply_2(v_zsmul_7475_, v_k_7477_, v___x_7480_);
        v___x_7482_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(
            v_inst_7463_,
            v_ctx_7464_,
            v_p_7479_,
        );
        v___x_7483_ = crate::leanh::lean_apply_2(v_toAdd_7476_, v___x_7481_, v___x_7482_);
        return v___x_7483_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(
    mut v_inst_7484_: *mut crate::leanh::LeanObject,
    mut v_ctx_7485_: *mut crate::leanh::LeanObject,
    mut v_p_7486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7487_ =
        l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_7484_, v_ctx_7485_, v_p_7486_);
    crate::leanh::lean_dec_ref(v_ctx_7485_);
    return v_res_7487_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule(
    mut v_00_u03b1_7488_: *mut crate::leanh::LeanObject,
    mut v_inst_7489_: *mut crate::leanh::LeanObject,
    mut v_ctx_7490_: *mut crate::leanh::LeanObject,
    mut v_p_7491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7492_ =
        l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_7489_, v_ctx_7490_, v_p_7491_);
    return v___x_7492_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(
    mut v_00_u03b1_7493_: *mut crate::leanh::LeanObject,
    mut v_inst_7494_: *mut crate::leanh::LeanObject,
    mut v_ctx_7495_: *mut crate::leanh::LeanObject,
    mut v_p_7496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7497_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(
        v_00_u03b1_7493_,
        v_inst_7494_,
        v_ctx_7495_,
        v_p_7496_,
    );
    crate::leanh::lean_dec_ref(v_ctx_7495_);
    return v_res_7497_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__gcd__cert(
    mut v_a_7498_: *mut crate::leanh::LeanObject,
    mut v_b_7499_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_7500_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_7501_: *mut crate::leanh::LeanObject,
    mut v_p_7502_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_u2081_7500_) == 0 {
        if crate::leanh::lean_obj_tag(v_p_u2082_7501_) == 0 {
            if crate::leanh::lean_obj_tag(v_p_7502_) == 0 {
                let mut v_k_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_k_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7509_: u8 = 0;
                v_k_7503_ = crate::leanh::lean_ctor_get(v_p_u2081_7500_, 0);
                v_k_7504_ = crate::leanh::lean_ctor_get(v_p_u2082_7501_, 0);
                v_k_7505_ = crate::leanh::lean_ctor_get(v_p_7502_, 0);
                v___x_7506_ = lean_int_mul(v_a_7498_, v_k_7503_);
                v___x_7507_ = lean_int_mul(v_b_7499_, v_k_7504_);
                v___x_7508_ = lean_int_add(v___x_7506_, v___x_7507_);
                crate::leanh::lean_dec(v___x_7507_);
                crate::leanh::lean_dec(v___x_7506_);
                v___x_7509_ = lean_int_dec_eq(v_k_7505_, v___x_7508_);
                crate::leanh::lean_dec(v___x_7508_);
                return v___x_7509_;
            } else {
                let mut v___x_7510_: u8 = 0;
                v___x_7510_ = 0;
                return v___x_7510_;
            }
        } else {
            let mut v___x_7511_: u8 = 0;
            v___x_7511_ = 0;
            return v___x_7511_;
        }
    } else {
        let mut v___x_7512_: u8 = 0;
        v___x_7512_ = 0;
        return v___x_7512_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_eq__gcd__cert___boxed(
    mut v_a_7513_: *mut crate::leanh::LeanObject,
    mut v_b_7514_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_7515_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_7516_: *mut crate::leanh::LeanObject,
    mut v_p_7517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7518_: u8 = 0;
    let mut v_r_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7518_ = l_Lean_Grind_CommRing_eq__gcd__cert(
        v_a_7513_,
        v_b_7514_,
        v_p_u2081_7515_,
        v_p_u2082_7516_,
        v_p_7517_,
    );
    crate::leanh::lean_dec_ref(v_p_7517_);
    crate::leanh::lean_dec_ref(v_p_u2082_7516_);
    crate::leanh::lean_dec_ref(v_p_u2081_7515_);
    crate::leanh::lean_dec(v_b_7514_);
    crate::leanh::lean_dec(v_a_7513_);
    v_r_7519_ = crate::leanh::lean_box((v_res_7518_) as usize);
    return v_r_7519_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(
    mut v_p_7520_: *mut crate::leanh::LeanObject,
    mut v_h__1_7521_: *mut crate::leanh::LeanObject,
    mut v_h__2_7522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_7520_) == 0 {
        let mut v_k_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7521_);
        v_k_7523_ = crate::leanh::lean_ctor_get(v_p_7520_, 0);
        crate::leanh::lean_inc(v_k_7523_);
        crate::leanh::lean_dec_ref_known(v_p_7520_, 1);
        v___x_7524_ = crate::leanh::lean_apply_1(v_h__2_7522_, v_k_7523_);
        return v___x_7524_;
    } else {
        let mut v_k_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7522_);
        v_k_7525_ = crate::leanh::lean_ctor_get(v_p_7520_, 0);
        crate::leanh::lean_inc(v_k_7525_);
        v_v_7526_ = crate::leanh::lean_ctor_get(v_p_7520_, 1);
        crate::leanh::lean_inc(v_v_7526_);
        v_p_7527_ = crate::leanh::lean_ctor_get(v_p_7520_, 2);
        crate::leanh::lean_inc_ref(v_p_7527_);
        crate::leanh::lean_dec_ref_known(v_p_7520_, 3);
        v___x_7528_ = crate::leanh::lean_apply_3(v_h__1_7521_, v_k_7525_, v_v_7526_, v_p_7527_);
        return v___x_7528_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(
    mut v_motive_7529_: *mut crate::leanh::LeanObject,
    mut v_p_7530_: *mut crate::leanh::LeanObject,
    mut v_h__1_7531_: *mut crate::leanh::LeanObject,
    mut v_h__2_7532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_7530_) == 0 {
        let mut v_k_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7531_);
        v_k_7533_ = crate::leanh::lean_ctor_get(v_p_7530_, 0);
        crate::leanh::lean_inc(v_k_7533_);
        crate::leanh::lean_dec_ref_known(v_p_7530_, 1);
        v___x_7534_ = crate::leanh::lean_apply_1(v_h__2_7532_, v_k_7533_);
        return v___x_7534_;
    } else {
        let mut v_k_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7532_);
        v_k_7535_ = crate::leanh::lean_ctor_get(v_p_7530_, 0);
        crate::leanh::lean_inc(v_k_7535_);
        v_v_7536_ = crate::leanh::lean_ctor_get(v_p_7530_, 1);
        crate::leanh::lean_inc(v_v_7536_);
        v_p_7537_ = crate::leanh::lean_ctor_get(v_p_7530_, 2);
        crate::leanh::lean_inc_ref(v_p_7537_);
        crate::leanh::lean_dec_ref_known(v_p_7530_, 3);
        v___x_7538_ = crate::leanh::lean_apply_3(v_h__1_7531_, v_k_7535_, v_v_7536_, v_p_7537_);
        return v___x_7538_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_CommSolver(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Field(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Int(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ordered_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Grind_CommRing_instInhabitedExpr_default =
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr_default);
    l_Lean_Grind_CommRing_instInhabitedExpr = _init_l_Lean_Grind_CommRing_instInhabitedExpr();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr);
    l_Lean_Grind_CommRing_instInhabitedMon_default =
        _init_l_Lean_Grind_CommRing_instInhabitedMon_default();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon_default);
    l_Lean_Grind_CommRing_instInhabitedMon = _init_l_Lean_Grind_CommRing_instInhabitedMon();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon);
    l_Lean_Grind_CommRing_hugeFuel = _init_l_Lean_Grind_CommRing_hugeFuel();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_hugeFuel);
    l_Lean_Grind_CommRing_instInhabitedPoly_default =
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly_default);
    l_Lean_Grind_CommRing_instInhabitedPoly = _init_l_Lean_Grind_CommRing_instInhabitedPoly();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ring_CommSolver(
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
pub unsafe fn initialize_Init_Grind_Ring_CommSolver(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Field(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_Int(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ordered_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_CommSolver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Ring_CommSolver(builtin);
}
