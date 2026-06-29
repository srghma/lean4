// Lean compiler output
// Module: Init.Grind.Ordered.Linarith
// Imports: Init.Grind.Ordered.Ring Init.Grind.Ring.Field Init.Data.Ord.Basic Init.Data.AC Init.LawfulBEqTactics Init.Data.Bool Init.Data.RArray Init.Data.Int.DivMod.Lemmas Init.Data.Nat.Lemmas Init.Grind.Ordered.Order Init.Omega Init.WFTactics Init.Data.Int.Repr
use crate::r#gen::Init::Data::AC::{initialize_Init_Data_AC, runtime_initialize_Init_Data_AC};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Repr::{
    initialize_Init_Data_Int_Repr, l_Int_repr, runtime_initialize_Init_Data_Int_Repr,
};
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, l_Lean_RArray_getImpl___redArg,
    runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Grind::Module::Basic::l_Lean_Grind_IntModule_toNatModule___redArg;
use crate::r#gen::Init::Grind::Ordered::Order::{
    initialize_Init_Grind_Ordered_Order, runtime_initialize_Init_Grind_Ordered_Order,
};
use crate::r#gen::Init::Grind::Ordered::Ring::{
    initialize_Init_Grind_Ordered_Ring, runtime_initialize_Init_Grind_Ordered_Ring,
};
use crate::r#gen::Init::Grind::Ring::Field::{
    initialize_Init_Grind_Ring_Field, runtime_initialize_Init_Grind_Ring_Field,
};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt};
pub static mut l_Lean_Grind_Linarith_instInhabitedExpr_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_Linarith_instInhabitedExpr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_instBEqExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_Linarith_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Linarith_instBEqExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Linarith_instBEqExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 122, 101, 114, 111, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value:
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
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value:
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
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value:
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
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 115, 117, 98, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value:
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
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 110, 97, 116, 77, 117, 108, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        69, 120, 112, 114, 46, 105, 110, 116, 77, 117, 108, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_instReprExpr___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Grind_Linarith_instReprExpr_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_Linarith_instReprExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Linarith_instReprExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instBEqPoly___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_Linarith_instBEqPoly_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Linarith_instBEqPoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Linarith_instBEqPoly: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value:
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
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        80, 111, 108, 121, 46, 110, 105, 108, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value:
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
        76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46,
        80, 111, 108, 121, 46, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Grind_Linarith_instReprPoly_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_Linarith_instReprPoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Linarith_instReprPoly: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_diseq__split__cert___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorIdx(
    mut v_x_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1245_) {
        0 => {
            let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1246_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1246_;
        }
        1 => {
            let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1247_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1247_;
        }
        2 => {
            let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1248_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1248_;
        }
        3 => {
            let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1249_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1249_;
        }
        4 => {
            let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1250_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1250_;
        }
        5 => {
            let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1251_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1251_;
        }
        _ => {
            let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1252_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1252_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorIdx___boxed(
    mut v_x_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lean_Grind_Linarith_Expr_ctorIdx(v_x_1253_);
    crate::leanh::lean_dec(v_x_1253_);
    return v_res_1254_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorElim___redArg(
    mut v_t_1255_: *mut crate::leanh::LeanObject,
    mut v_k_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1255_) {
        0 => {
            return v_k_1256_;
        }
        1 => {
            let mut v_i_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_1257_ = crate::leanh::lean_ctor_get(v_t_1255_, 0);
            crate::leanh::lean_inc(v_i_1257_);
            crate::leanh::lean_dec_ref_known(v_t_1255_, 1);
            v___x_1258_ = crate::leanh::lean_apply_1(v_k_1256_, v_i_1257_);
            return v___x_1258_;
        }
        4 => {
            let mut v_a_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1259_ = crate::leanh::lean_ctor_get(v_t_1255_, 0);
            crate::leanh::lean_inc(v_a_1259_);
            crate::leanh::lean_dec_ref_known(v_t_1255_, 1);
            v___x_1260_ = crate::leanh::lean_apply_1(v_k_1256_, v_a_1259_);
            return v___x_1260_;
        }
        _ => {
            let mut v_a_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1261_ = crate::leanh::lean_ctor_get(v_t_1255_, 0);
            crate::leanh::lean_inc(v_a_1261_);
            v_b_1262_ = crate::leanh::lean_ctor_get(v_t_1255_, 1);
            crate::leanh::lean_inc(v_b_1262_);
            crate::leanh::lean_dec(v_t_1255_);
            v___x_1263_ = crate::leanh::lean_apply_2(v_k_1256_, v_a_1261_, v_b_1262_);
            return v___x_1263_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorElim(
    mut v_motive_1264_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1265_: *mut crate::leanh::LeanObject,
    mut v_t_1266_: *mut crate::leanh::LeanObject,
    mut v_h_1267_: *mut crate::leanh::LeanObject,
    mut v_k_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1266_, v_k_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorElim___boxed(
    mut v_motive_1270_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1271_: *mut crate::leanh::LeanObject,
    mut v_t_1272_: *mut crate::leanh::LeanObject,
    mut v_h_1273_: *mut crate::leanh::LeanObject,
    mut v_k_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_Grind_Linarith_Expr_ctorElim(
        v_motive_1270_,
        v_ctorIdx_1271_,
        v_t_1272_,
        v_h_1273_,
        v_k_1274_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1271_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_zero_elim___redArg(
    mut v_t_1276_: *mut crate::leanh::LeanObject,
    mut v_zero_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1276_, v_zero_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_zero_elim(
    mut v_motive_1279_: *mut crate::leanh::LeanObject,
    mut v_t_1280_: *mut crate::leanh::LeanObject,
    mut v_h_1281_: *mut crate::leanh::LeanObject,
    mut v_zero_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1280_, v_zero_1282_);
    return v___x_1283_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_var_elim___redArg(
    mut v_t_1284_: *mut crate::leanh::LeanObject,
    mut v_var_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1284_, v_var_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_var_elim(
    mut v_motive_1287_: *mut crate::leanh::LeanObject,
    mut v_t_1288_: *mut crate::leanh::LeanObject,
    mut v_h_1289_: *mut crate::leanh::LeanObject,
    mut v_var_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1288_, v_var_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_add_elim___redArg(
    mut v_t_1292_: *mut crate::leanh::LeanObject,
    mut v_add_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1292_, v_add_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_add_elim(
    mut v_motive_1295_: *mut crate::leanh::LeanObject,
    mut v_t_1296_: *mut crate::leanh::LeanObject,
    mut v_h_1297_: *mut crate::leanh::LeanObject,
    mut v_add_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1296_, v_add_1298_);
    return v___x_1299_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_sub_elim___redArg(
    mut v_t_1300_: *mut crate::leanh::LeanObject,
    mut v_sub_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1300_, v_sub_1301_);
    return v___x_1302_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_sub_elim(
    mut v_motive_1303_: *mut crate::leanh::LeanObject,
    mut v_t_1304_: *mut crate::leanh::LeanObject,
    mut v_h_1305_: *mut crate::leanh::LeanObject,
    mut v_sub_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1307_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1304_, v_sub_1306_);
    return v___x_1307_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_neg_elim___redArg(
    mut v_t_1308_: *mut crate::leanh::LeanObject,
    mut v_neg_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1308_, v_neg_1309_);
    return v___x_1310_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_neg_elim(
    mut v_motive_1311_: *mut crate::leanh::LeanObject,
    mut v_t_1312_: *mut crate::leanh::LeanObject,
    mut v_h_1313_: *mut crate::leanh::LeanObject,
    mut v_neg_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1312_, v_neg_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_natMul_elim___redArg(
    mut v_t_1316_: *mut crate::leanh::LeanObject,
    mut v_natMul_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1316_, v_natMul_1317_);
    return v___x_1318_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_natMul_elim(
    mut v_motive_1319_: *mut crate::leanh::LeanObject,
    mut v_t_1320_: *mut crate::leanh::LeanObject,
    mut v_h_1321_: *mut crate::leanh::LeanObject,
    mut v_natMul_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1320_, v_natMul_1322_);
    return v___x_1323_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_intMul_elim___redArg(
    mut v_t_1324_: *mut crate::leanh::LeanObject,
    mut v_intMul_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1324_, v_intMul_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_intMul_elim(
    mut v_motive_1327_: *mut crate::leanh::LeanObject,
    mut v_t_1328_: *mut crate::leanh::LeanObject,
    mut v_h_1329_: *mut crate::leanh::LeanObject,
    mut v_intMul_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1328_, v_intMul_1330_);
    return v___x_1331_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instInhabitedExpr_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = crate::leanh::lean_box(0);
    return v___x_1332_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instInhabitedExpr() -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = crate::leanh::lean_box(0);
    return v___x_1333_;
}
pub unsafe fn l_Lean_Grind_Linarith_instBEqExpr_beq(
    mut v_x_1334_: *mut crate::leanh::LeanObject,
    mut v_x_1335_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: u8 = 0;
    let mut v_i_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v_a_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut v_a_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v_a_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u8 = 0;
    let mut v_k_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: u8 = 0;
    let mut v___x_1369_: u8 = 0;
    let mut v_k_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1334_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 0 {
                        v___x_1343_ = 1;
                        return v___x_1343_;
                    } else {
                        v___x_1344_ = 0;
                        return v___x_1344_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 1 {
                        v_i_1345_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                        v_i_1346_ = crate::leanh::lean_ctor_get(v_x_1335_, 0);
                        v___x_1347_ = lean_nat_dec_eq(v_i_1345_, v_i_1346_);
                        return v___x_1347_;
                    } else {
                        v___x_1348_ = 0;
                        return v___x_1348_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 2 {
                        v_a_1349_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                        v_b_1350_ = crate::leanh::lean_ctor_get(v_x_1334_, 1);
                        v_a_1351_ = crate::leanh::lean_ctor_get(v_x_1335_, 0);
                        v_b_1352_ = crate::leanh::lean_ctor_get(v_x_1335_, 1);
                        v_a_1337_ = v_a_1349_;
                        v_a_1338_ = v_b_1350_;
                        v_b_1339_ = v_a_1351_;
                        v_b_1340_ = v_b_1352_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1353_ = 0;
                        return v___x_1353_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 3 {
                        v_a_1354_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                        v_b_1355_ = crate::leanh::lean_ctor_get(v_x_1334_, 1);
                        v_a_1356_ = crate::leanh::lean_ctor_get(v_x_1335_, 0);
                        v_b_1357_ = crate::leanh::lean_ctor_get(v_x_1335_, 1);
                        v_a_1337_ = v_a_1354_;
                        v_a_1338_ = v_b_1355_;
                        v_b_1339_ = v_a_1356_;
                        v_b_1340_ = v_b_1357_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1358_ = 0;
                        return v___x_1358_;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 4 {
                        v_a_1359_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                        v_a_1360_ = crate::leanh::lean_ctor_get(v_x_1335_, 0);
                        v_x_1334_ = v_a_1359_;
                        v_x_1335_ = v_a_1360_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1362_ = 0;
                        return v___x_1362_;
                    }
                }
                5 => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 5 {
                        v_k_1363_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                        v_a_1364_ = crate::leanh::lean_ctor_get(v_x_1334_, 1);
                        v_k_1365_ = crate::leanh::lean_ctor_get(v_x_1335_, 0);
                        v_a_1366_ = crate::leanh::lean_ctor_get(v_x_1335_, 1);
                        v___x_1367_ = lean_nat_dec_eq(v_k_1363_, v_k_1365_);
                        if v___x_1367_ == 0 {
                            return v___x_1367_;
                        } else {
                            v_x_1334_ = v_a_1364_;
                            v_x_1335_ = v_a_1366_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1369_ = 0;
                        return v___x_1369_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_1335_) == 6 {
                        v_k_1370_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                        v_a_1371_ = crate::leanh::lean_ctor_get(v_x_1334_, 1);
                        v_k_1372_ = crate::leanh::lean_ctor_get(v_x_1335_, 0);
                        v_a_1373_ = crate::leanh::lean_ctor_get(v_x_1335_, 1);
                        v___x_1374_ = lean_int_dec_eq(v_k_1370_, v_k_1372_);
                        if v___x_1374_ == 0 {
                            return v___x_1374_;
                        } else {
                            v_x_1334_ = v_a_1371_;
                            v_x_1335_ = v_a_1373_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1376_ = 0;
                        return v___x_1376_;
                    }
                }
            },
            1 => {
                v___x_1341_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_a_1337_, v_b_1339_);
                if v___x_1341_ == 0 {
                    return v___x_1341_;
                } else {
                    v_x_1334_ = v_a_1338_;
                    v_x_1335_ = v_b_1340_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_instBEqExpr_beq___boxed(
    mut v_x_1377_: *mut crate::leanh::LeanObject,
    mut v_x_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1379_: u8 = 0;
    let mut v_r_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_x_1377_, v_x_1378_);
    crate::leanh::lean_dec(v_x_1378_);
    crate::leanh::lean_dec(v_x_1377_);
    v_r_1380_ = crate::leanh::lean_box((v_res_1379_) as usize);
    return v_r_1380_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1387_ = lean_nat_to_int(v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1389_ = lean_nat_to_int(v___x_1388_);
    return v___x_1389_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1427_ = lean_nat_to_int(v___x_1426_);
    return v___x_1427_;
}
pub unsafe fn l_Lean_Grind_Linarith_instReprExpr_repr(
    mut v_x_1428_: *mut crate::leanh::LeanObject,
    mut v_prec_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: u8 = 0;
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___y_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_a_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: u8 = 0;
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut v_k_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1428_) {
                0 => {
                    v___x_1437_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1438_ = lean_nat_dec_le(v___x_1437_, v_prec_1429_);
                    if v___x_1438_ == 0 {
                        v___x_1439_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                        );
                        v___y_1431_ = v___x_1439_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1440_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                        );
                        v___y_1431_ = v___x_1440_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_1441_ = crate::leanh::lean_ctor_get(v_x_1428_, 0);
                    v_isSharedCheck_1461_ = (!crate::leanh::lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1443_ = v_x_1428_;
                        v_isShared_1444_ = v_isSharedCheck_1461_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_1441_);
                        crate::leanh::lean_dec(v_x_1428_);
                        v___x_1443_ = crate::leanh::lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1461_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_a_1462_ = crate::leanh::lean_ctor_get(v_x_1428_, 0);
                    v_b_1463_ = crate::leanh::lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1486_ = (!crate::leanh::lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1465_ = v_x_1428_;
                        v_isShared_1466_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_1463_);
                        crate::leanh::lean_inc(v_a_1462_);
                        crate::leanh::lean_dec(v_x_1428_);
                        v___x_1465_ = crate::leanh::lean_box(0);
                        v_isShared_1466_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_a_1487_ = crate::leanh::lean_ctor_get(v_x_1428_, 0);
                    v_b_1488_ = crate::leanh::lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1511_ = (!crate::leanh::lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1511_ == 0 {
                        v___x_1490_ = v_x_1428_;
                        v_isShared_1491_ = v_isSharedCheck_1511_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_1488_);
                        crate::leanh::lean_inc(v_a_1487_);
                        crate::leanh::lean_dec(v_x_1428_);
                        v___x_1490_ = crate::leanh::lean_box(0);
                        v_isShared_1491_ = v_isSharedCheck_1511_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    v_a_1512_ = crate::leanh::lean_ctor_get(v_x_1428_, 0);
                    crate::leanh::lean_inc(v_a_1512_);
                    crate::leanh::lean_dec_ref_known(v_x_1428_, 1);
                    v___x_1513_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1523_ = lean_nat_dec_le(v___x_1513_, v_prec_1429_);
                    if v___x_1523_ == 0 {
                        v___x_1524_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                        );
                        v___y_1515_ = v___x_1524_;
                        state = 11;
                        continue;
                    } else {
                        v___x_1525_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                        );
                        v___y_1515_ = v___x_1525_;
                        state = 11;
                        continue;
                    }
                }
                5 => {
                    v_k_1526_ = crate::leanh::lean_ctor_get(v_x_1428_, 0);
                    v_a_1527_ = crate::leanh::lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1551_ = (!crate::leanh::lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1551_ == 0 {
                        v___x_1529_ = v_x_1428_;
                        v_isShared_1530_ = v_isSharedCheck_1551_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1527_);
                        crate::leanh::lean_inc(v_k_1526_);
                        crate::leanh::lean_dec(v_x_1428_);
                        v___x_1529_ = crate::leanh::lean_box(0);
                        v_isShared_1530_ = v_isSharedCheck_1551_;
                        state = 12;
                        continue;
                    }
                }
                _ => {
                    v_k_1552_ = crate::leanh::lean_ctor_get(v_x_1428_, 0);
                    v_a_1553_ = crate::leanh::lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1587_ = (!crate::leanh::lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1555_ = v_x_1428_;
                        v_isShared_1556_ = v_isSharedCheck_1587_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1553_);
                        crate::leanh::lean_inc(v_k_1552_);
                        crate::leanh::lean_dec(v_x_1428_);
                        v___x_1555_ = crate::leanh::lean_box(0);
                        v_isShared_1556_ = v_isSharedCheck_1587_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1432_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__1;
                crate::leanh::lean_inc(v___y_1431_);
                v___x_1433_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1433_, 0, v___y_1431_);
                crate::leanh::lean_ctor_set(v___x_1433_, 1, v___x_1432_);
                v___x_1434_ = 0;
                v___x_1435_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1433_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1435_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1434_,
                );
                v___x_1436_ = l_Repr_addAppParen(v___x_1435_, v_prec_1429_);
                return v___x_1436_;
            }
            2 => {
                v___x_1457_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1458_ = lean_nat_dec_le(v___x_1457_, v_prec_1429_);
                if v___x_1458_ == 0 {
                    v___x_1459_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                    );
                    v___y_1446_ = v___x_1459_;
                    state = 3;
                    continue;
                } else {
                    v___x_1460_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                    );
                    v___y_1446_ = v___x_1460_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1447_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__6;
                v___x_1448_ = l_Nat_reprFast(v_i_1441_);
                if v_isShared_1444_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1443_, 3);
                    crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1448_);
                    v___x_1450_ = v___x_1443_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1456_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1448_);
                    v___x_1450_ = v_reuseFailAlloc_1456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1451_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1447_);
                crate::leanh::lean_ctor_set(v___x_1451_, 1, v___x_1450_);
                crate::leanh::lean_inc(v___y_1446_);
                v___x_1452_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1452_, 0, v___y_1446_);
                crate::leanh::lean_ctor_set(v___x_1452_, 1, v___x_1451_);
                v___x_1453_ = 0;
                v___x_1454_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1454_, 0, v___x_1452_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1454_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1453_,
                );
                v___x_1455_ = l_Repr_addAppParen(v___x_1454_, v_prec_1429_);
                return v___x_1455_;
            }
            5 => {
                v___x_1467_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1483_ = lean_nat_dec_le(v___x_1467_, v_prec_1429_);
                if v___x_1483_ == 0 {
                    v___x_1484_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                    );
                    v___y_1469_ = v___x_1484_;
                    state = 6;
                    continue;
                } else {
                    v___x_1485_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                    );
                    v___y_1469_ = v___x_1485_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1470_ = crate::leanh::lean_box(1);
                v___x_1471_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__9;
                v___x_1472_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1462_, v___x_1467_);
                if v_isShared_1466_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1465_, 5);
                    crate::leanh::lean_ctor_set(v___x_1465_, 1, v___x_1472_);
                    crate::leanh::lean_ctor_set(v___x_1465_, 0, v___x_1471_);
                    v___x_1474_ = v___x_1465_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1472_);
                    v___x_1474_ = v_reuseFailAlloc_1482_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1475_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                crate::leanh::lean_ctor_set(v___x_1475_, 1, v___x_1470_);
                v___x_1476_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_1463_, v___x_1467_);
                v___x_1477_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1475_);
                crate::leanh::lean_ctor_set(v___x_1477_, 1, v___x_1476_);
                crate::leanh::lean_inc(v___y_1469_);
                v___x_1478_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1478_, 0, v___y_1469_);
                crate::leanh::lean_ctor_set(v___x_1478_, 1, v___x_1477_);
                v___x_1479_ = 0;
                v___x_1480_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1480_, 0, v___x_1478_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1480_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1479_,
                );
                v___x_1481_ = l_Repr_addAppParen(v___x_1480_, v_prec_1429_);
                return v___x_1481_;
            }
            8 => {
                v___x_1492_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1508_ = lean_nat_dec_le(v___x_1492_, v_prec_1429_);
                if v___x_1508_ == 0 {
                    v___x_1509_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                    );
                    v___y_1494_ = v___x_1509_;
                    state = 9;
                    continue;
                } else {
                    v___x_1510_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                    );
                    v___y_1494_ = v___x_1510_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1495_ = crate::leanh::lean_box(1);
                v___x_1496_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__12;
                v___x_1497_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1487_, v___x_1492_);
                if v_isShared_1491_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1490_, 5);
                    crate::leanh::lean_ctor_set(v___x_1490_, 1, v___x_1497_);
                    crate::leanh::lean_ctor_set(v___x_1490_, 0, v___x_1496_);
                    v___x_1499_ = v___x_1490_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1497_);
                    v___x_1499_ = v_reuseFailAlloc_1507_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1500_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1499_);
                crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1495_);
                v___x_1501_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_1488_, v___x_1492_);
                v___x_1502_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1502_, 0, v___x_1500_);
                crate::leanh::lean_ctor_set(v___x_1502_, 1, v___x_1501_);
                crate::leanh::lean_inc(v___y_1494_);
                v___x_1503_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1503_, 0, v___y_1494_);
                crate::leanh::lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                v___x_1504_ = 0;
                v___x_1505_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1504_,
                );
                v___x_1506_ = l_Repr_addAppParen(v___x_1505_, v_prec_1429_);
                return v___x_1506_;
            }
            11 => {
                v___x_1516_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__15;
                v___x_1517_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1512_, v___x_1513_);
                v___x_1518_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1516_);
                crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                crate::leanh::lean_inc(v___y_1515_);
                v___x_1519_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1519_, 0, v___y_1515_);
                crate::leanh::lean_ctor_set(v___x_1519_, 1, v___x_1518_);
                v___x_1520_ = 0;
                v___x_1521_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1521_, 0, v___x_1519_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1521_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1520_,
                );
                v___x_1522_ = l_Repr_addAppParen(v___x_1521_, v_prec_1429_);
                return v___x_1522_;
            }
            12 => {
                v___x_1531_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1548_ = lean_nat_dec_le(v___x_1531_, v_prec_1429_);
                if v___x_1548_ == 0 {
                    v___x_1549_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                    );
                    v___y_1533_ = v___x_1549_;
                    state = 13;
                    continue;
                } else {
                    v___x_1550_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                    );
                    v___y_1533_ = v___x_1550_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1534_ = crate::leanh::lean_box(1);
                v___x_1535_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__18;
                v___x_1536_ = l_Nat_reprFast(v_k_1526_);
                v___x_1537_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                if v_isShared_1530_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1529_, 1, v___x_1537_);
                    crate::leanh::lean_ctor_set(v___x_1529_, 0, v___x_1535_);
                    v___x_1539_ = v___x_1529_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1537_);
                    v___x_1539_ = v_reuseFailAlloc_1547_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1540_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1540_, 1, v___x_1534_);
                v___x_1541_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1527_, v___x_1531_);
                v___x_1542_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1540_);
                crate::leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
                crate::leanh::lean_inc(v___y_1533_);
                v___x_1543_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1543_, 0, v___y_1533_);
                crate::leanh::lean_ctor_set(v___x_1543_, 1, v___x_1542_);
                v___x_1544_ = 0;
                v___x_1545_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1545_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1544_,
                );
                v___x_1546_ = l_Repr_addAppParen(v___x_1545_, v_prec_1429_);
                return v___x_1546_;
            }
            15 => {
                v___x_1557_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1584_ = lean_nat_dec_le(v___x_1557_, v_prec_1429_);
                if v___x_1584_ == 0 {
                    v___x_1585_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                    );
                    v___y_1574_ = v___x_1585_;
                    state = 18;
                    continue;
                } else {
                    v___x_1586_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                    );
                    v___y_1574_ = v___x_1586_;
                    state = 18;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_inc(v___y_1559_);
                if v_isShared_1556_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1555_, 5);
                    crate::leanh::lean_ctor_set(v___x_1555_, 1, v___y_1562_);
                    crate::leanh::lean_ctor_set(v___x_1555_, 0, v___y_1559_);
                    v___x_1564_ = v___x_1555_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1572_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___y_1559_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___y_1562_);
                    v___x_1564_ = v_reuseFailAlloc_1572_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_inc(v___y_1561_);
                v___x_1565_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
                crate::leanh::lean_ctor_set(v___x_1565_, 1, v___y_1561_);
                v___x_1566_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1553_, v___x_1557_);
                v___x_1567_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1567_, 0, v___x_1565_);
                crate::leanh::lean_ctor_set(v___x_1567_, 1, v___x_1566_);
                crate::leanh::lean_inc(v___y_1560_);
                v___x_1568_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1568_, 0, v___y_1560_);
                crate::leanh::lean_ctor_set(v___x_1568_, 1, v___x_1567_);
                v___x_1569_ = 0;
                v___x_1570_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1568_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1570_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1569_,
                );
                v___x_1571_ = l_Repr_addAppParen(v___x_1570_, v_prec_1429_);
                return v___x_1571_;
            }
            18 => {
                v___x_1575_ = crate::leanh::lean_box(1);
                v___x_1576_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__21;
                v___x_1577_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                v___x_1578_ = lean_int_dec_lt(v_k_1552_, v___x_1577_);
                if v___x_1578_ == 0 {
                    v___x_1579_ = l_Int_repr(v_k_1552_);
                    crate::leanh::lean_dec(v_k_1552_);
                    v___x_1580_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1580_, 0, v___x_1579_);
                    v___y_1559_ = v___x_1576_;
                    v___y_1560_ = v___y_1574_;
                    v___y_1561_ = v___x_1575_;
                    v___y_1562_ = v___x_1580_;
                    state = 16;
                    continue;
                } else {
                    v___x_1581_ = l_Int_repr(v_k_1552_);
                    crate::leanh::lean_dec(v_k_1552_);
                    v___x_1582_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1581_);
                    v___x_1583_ = l_Repr_addAppParen(v___x_1582_, v___x_1557_);
                    v___y_1559_ = v___x_1576_;
                    v___y_1560_ = v___y_1574_;
                    v___y_1561_ = v___x_1575_;
                    v___y_1562_ = v___x_1583_;
                    state = 16;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_instReprExpr_repr___boxed(
    mut v_x_1588_: *mut crate::leanh::LeanObject,
    mut v_prec_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_x_1588_, v_prec_1589_);
    crate::leanh::lean_dec(v_prec_1589_);
    return v_res_1590_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote___redArg(
    mut v_ctx_1593_: *mut crate::leanh::LeanObject,
    mut v_v_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = l_Lean_RArray_getImpl___redArg(v_ctx_1593_, v_v_1594_);
    return v___x_1595_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote___redArg___boxed(
    mut v_ctx_1596_: *mut crate::leanh::LeanObject,
    mut v_v_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Grind_Linarith_Var_denote___redArg(v_ctx_1596_, v_v_1597_);
    crate::leanh::lean_dec(v_v_1597_);
    crate::leanh::lean_dec_ref(v_ctx_1596_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote(
    mut v_00_u03b1_1599_: *mut crate::leanh::LeanObject,
    mut v_ctx_1600_: *mut crate::leanh::LeanObject,
    mut v_v_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_RArray_getImpl___redArg(v_ctx_1600_, v_v_1601_);
    return v___x_1602_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote___boxed(
    mut v_00_u03b1_1603_: *mut crate::leanh::LeanObject,
    mut v_ctx_1604_: *mut crate::leanh::LeanObject,
    mut v_v_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Lean_Grind_Linarith_Var_denote(v_00_u03b1_1603_, v_ctx_1604_, v_v_1605_);
    crate::leanh::lean_dec(v_v_1605_);
    crate::leanh::lean_dec_ref(v_ctx_1604_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote___redArg(
    mut v_inst_1607_: *mut crate::leanh::LeanObject,
    mut v_ctx_1608_: *mut crate::leanh::LeanObject,
    mut v_x_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1607_);
    v_toAddCommMonoid_1611_ = crate::leanh::lean_ctor_get(v___x_1610_, 0);
    crate::leanh::lean_inc_ref(v_toAddCommMonoid_1611_);
    match crate::leanh::lean_obj_tag(v_x_1609_) {
        0 => {
            let mut v_toZero_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_1610_);
            crate::leanh::lean_dec_ref(v_inst_1607_);
            v_toZero_1612_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1611_, 0);
            crate::leanh::lean_inc(v_toZero_1612_);
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            return v_toZero_1612_;
        }
        1 => {
            let mut v_i_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            crate::leanh::lean_dec_ref(v___x_1610_);
            crate::leanh::lean_dec_ref(v_inst_1607_);
            v_i_1613_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
            crate::leanh::lean_inc(v_i_1613_);
            crate::leanh::lean_dec_ref_known(v_x_1609_, 1);
            v___x_1614_ = l_Lean_RArray_getImpl___redArg(v_ctx_1608_, v_i_1613_);
            crate::leanh::lean_dec(v_i_1613_);
            return v___x_1614_;
        }
        2 => {
            let mut v_toAdd_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_1610_);
            v_toAdd_1615_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1611_, 1);
            crate::leanh::lean_inc(v_toAdd_1615_);
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            v_a_1616_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
            crate::leanh::lean_inc(v_a_1616_);
            v_b_1617_ = crate::leanh::lean_ctor_get(v_x_1609_, 1);
            crate::leanh::lean_inc(v_b_1617_);
            crate::leanh::lean_dec_ref_known(v_x_1609_, 2);
            crate::leanh::lean_inc_ref(v_inst_1607_);
            v___x_1618_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1616_);
            v___x_1619_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_b_1617_);
            v___x_1620_ = crate::leanh::lean_apply_2(v_toAdd_1615_, v___x_1618_, v___x_1619_);
            return v___x_1620_;
        }
        3 => {
            let mut v_toAddCommGroup_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toSub_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toAddCommGroup_1621_ = crate::leanh::lean_ctor_get(v_inst_1607_, 0);
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            crate::leanh::lean_dec_ref(v___x_1610_);
            v_toSub_1622_ = crate::leanh::lean_ctor_get(v_toAddCommGroup_1621_, 2);
            crate::leanh::lean_inc(v_toSub_1622_);
            v_a_1623_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
            crate::leanh::lean_inc(v_a_1623_);
            v_b_1624_ = crate::leanh::lean_ctor_get(v_x_1609_, 1);
            crate::leanh::lean_inc(v_b_1624_);
            crate::leanh::lean_dec_ref_known(v_x_1609_, 2);
            crate::leanh::lean_inc_ref(v_inst_1607_);
            v___x_1625_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1623_);
            v___x_1626_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_b_1624_);
            v___x_1627_ = crate::leanh::lean_apply_2(v_toSub_1622_, v___x_1625_, v___x_1626_);
            return v___x_1627_;
        }
        4 => {
            let mut v_toAddCommGroup_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toNeg_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toAddCommGroup_1628_ = crate::leanh::lean_ctor_get(v_inst_1607_, 0);
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            crate::leanh::lean_dec_ref(v___x_1610_);
            v_toNeg_1629_ = crate::leanh::lean_ctor_get(v_toAddCommGroup_1628_, 1);
            crate::leanh::lean_inc(v_toNeg_1629_);
            v_a_1630_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
            crate::leanh::lean_inc(v_a_1630_);
            crate::leanh::lean_dec_ref_known(v_x_1609_, 1);
            v___x_1631_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1630_);
            v___x_1632_ = crate::leanh::lean_apply_1(v_toNeg_1629_, v___x_1631_);
            return v___x_1632_;
        }
        5 => {
            let mut v_nsmul_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            v_nsmul_1633_ = crate::leanh::lean_ctor_get(v___x_1610_, 1);
            crate::leanh::lean_inc(v_nsmul_1633_);
            crate::leanh::lean_dec_ref(v___x_1610_);
            v_k_1634_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
            crate::leanh::lean_inc(v_k_1634_);
            v_a_1635_ = crate::leanh::lean_ctor_get(v_x_1609_, 1);
            crate::leanh::lean_inc(v_a_1635_);
            crate::leanh::lean_dec_ref_known(v_x_1609_, 2);
            v___x_1636_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1635_);
            v___x_1637_ = crate::leanh::lean_apply_2(v_nsmul_1633_, v_k_1634_, v___x_1636_);
            return v___x_1637_;
        }
        _ => {
            let mut v_zsmul_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_toAddCommMonoid_1611_);
            crate::leanh::lean_dec_ref(v___x_1610_);
            v_zsmul_1638_ = crate::leanh::lean_ctor_get(v_inst_1607_, 2);
            crate::leanh::lean_inc(v_zsmul_1638_);
            v_k_1639_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
            crate::leanh::lean_inc(v_k_1639_);
            v_a_1640_ = crate::leanh::lean_ctor_get(v_x_1609_, 1);
            crate::leanh::lean_inc(v_a_1640_);
            crate::leanh::lean_dec_ref_known(v_x_1609_, 2);
            v___x_1641_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1640_);
            v___x_1642_ = crate::leanh::lean_apply_2(v_zsmul_1638_, v_k_1639_, v___x_1641_);
            return v___x_1642_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(
    mut v_inst_1643_: *mut crate::leanh::LeanObject,
    mut v_ctx_1644_: *mut crate::leanh::LeanObject,
    mut v_x_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1643_, v_ctx_1644_, v_x_1645_);
    crate::leanh::lean_dec_ref(v_ctx_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote(
    mut v_00_u03b1_1647_: *mut crate::leanh::LeanObject,
    mut v_inst_1648_: *mut crate::leanh::LeanObject,
    mut v_ctx_1649_: *mut crate::leanh::LeanObject,
    mut v_x_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1648_, v_ctx_1649_, v_x_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote___boxed(
    mut v_00_u03b1_1652_: *mut crate::leanh::LeanObject,
    mut v_inst_1653_: *mut crate::leanh::LeanObject,
    mut v_ctx_1654_: *mut crate::leanh::LeanObject,
    mut v_x_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1656_ =
        l_Lean_Grind_Linarith_Expr_denote(v_00_u03b1_1652_, v_inst_1653_, v_ctx_1654_, v_x_1655_);
    crate::leanh::lean_dec_ref(v_ctx_1654_);
    return v_res_1656_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorIdx(
    mut v_x_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1657_) == 0 {
        let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1658_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1658_;
    } else {
        let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1659_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1659_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorIdx___boxed(
    mut v_x_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1661_ = l_Lean_Grind_Linarith_Poly_ctorIdx(v_x_1660_);
    crate::leanh::lean_dec(v_x_1660_);
    return v_res_1661_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorElim___redArg(
    mut v_t_1662_: *mut crate::leanh::LeanObject,
    mut v_k_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1662_) == 0 {
        return v_k_1663_;
    } else {
        let mut v_k_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1664_ = crate::leanh::lean_ctor_get(v_t_1662_, 0);
        crate::leanh::lean_inc(v_k_1664_);
        v_v_1665_ = crate::leanh::lean_ctor_get(v_t_1662_, 1);
        crate::leanh::lean_inc(v_v_1665_);
        v_p_1666_ = crate::leanh::lean_ctor_get(v_t_1662_, 2);
        crate::leanh::lean_inc(v_p_1666_);
        crate::leanh::lean_dec_ref_known(v_t_1662_, 3);
        v___x_1667_ = crate::leanh::lean_apply_3(v_k_1663_, v_k_1664_, v_v_1665_, v_p_1666_);
        return v___x_1667_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorElim(
    mut v_motive_1668_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1669_: *mut crate::leanh::LeanObject,
    mut v_t_1670_: *mut crate::leanh::LeanObject,
    mut v_h_1671_: *mut crate::leanh::LeanObject,
    mut v_k_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1670_, v_k_1672_);
    return v___x_1673_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorElim___boxed(
    mut v_motive_1674_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1675_: *mut crate::leanh::LeanObject,
    mut v_t_1676_: *mut crate::leanh::LeanObject,
    mut v_h_1677_: *mut crate::leanh::LeanObject,
    mut v_k_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1679_ = l_Lean_Grind_Linarith_Poly_ctorElim(
        v_motive_1674_,
        v_ctorIdx_1675_,
        v_t_1676_,
        v_h_1677_,
        v_k_1678_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1675_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_nil_elim___redArg(
    mut v_t_1680_: *mut crate::leanh::LeanObject,
    mut v_nil_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1680_, v_nil_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_nil_elim(
    mut v_motive_1683_: *mut crate::leanh::LeanObject,
    mut v_t_1684_: *mut crate::leanh::LeanObject,
    mut v_h_1685_: *mut crate::leanh::LeanObject,
    mut v_nil_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1684_, v_nil_1686_);
    return v___x_1687_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_add_elim___redArg(
    mut v_t_1688_: *mut crate::leanh::LeanObject,
    mut v_add_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1688_, v_add_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_add_elim(
    mut v_motive_1691_: *mut crate::leanh::LeanObject,
    mut v_t_1692_: *mut crate::leanh::LeanObject,
    mut v_h_1693_: *mut crate::leanh::LeanObject,
    mut v_add_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1692_, v_add_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Lean_Grind_Linarith_instBEqPoly_beq(
    mut v_x_1696_: *mut crate::leanh::LeanObject,
    mut v_x_1697_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: u8 = 0;
    let mut v_k_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1696_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_1697_) == 0 {
                        v___x_1698_ = 1;
                        return v___x_1698_;
                    } else {
                        v___x_1699_ = 0;
                        return v___x_1699_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1697_) == 1 {
                        v_k_1700_ = crate::leanh::lean_ctor_get(v_x_1696_, 0);
                        v_v_1701_ = crate::leanh::lean_ctor_get(v_x_1696_, 1);
                        v_p_1702_ = crate::leanh::lean_ctor_get(v_x_1696_, 2);
                        v_k_1703_ = crate::leanh::lean_ctor_get(v_x_1697_, 0);
                        v_v_1704_ = crate::leanh::lean_ctor_get(v_x_1697_, 1);
                        v_p_1705_ = crate::leanh::lean_ctor_get(v_x_1697_, 2);
                        v___x_1706_ = lean_int_dec_eq(v_k_1700_, v_k_1703_);
                        if v___x_1706_ == 0 {
                            return v___x_1706_;
                        } else {
                            v___x_1707_ = lean_nat_dec_eq(v_v_1701_, v_v_1704_);
                            if v___x_1707_ == 0 {
                                return v___x_1707_;
                            } else {
                                v_x_1696_ = v_p_1702_;
                                v_x_1697_ = v_p_1705_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v___x_1709_ = 0;
                        return v___x_1709_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_instBEqPoly_beq___boxed(
    mut v_x_1710_: *mut crate::leanh::LeanObject,
    mut v_x_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: u8 = 0;
    let mut v_r_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_1710_, v_x_1711_);
    crate::leanh::lean_dec(v_x_1711_);
    crate::leanh::lean_dec(v_x_1710_);
    v_r_1713_ = crate::leanh::lean_box((v_res_1712_) as usize);
    return v_r_1713_;
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(
    mut v_x_1716_: *mut crate::leanh::LeanObject,
    mut v_x_1717_: *mut crate::leanh::LeanObject,
    mut v_h__1_1718_: *mut crate::leanh::LeanObject,
    mut v_h__2_1719_: *mut crate::leanh::LeanObject,
    mut v_h__3_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1716_) == 0 {
        crate::leanh::lean_dec(v_h__2_1719_);
        if crate::leanh::lean_obj_tag(v_x_1717_) == 0 {
            let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1720_);
            v___x_1721_ = crate::leanh::lean_box(0);
            v___x_1722_ = crate::leanh::lean_apply_1(v_h__1_1718_, v___x_1721_);
            return v___x_1722_;
        } else {
            let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1718_);
            v___x_1723_ = crate::leanh::lean_apply_4(
                v_h__3_1720_,
                v_x_1716_,
                v_x_1717_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1723_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_1718_);
        if crate::leanh::lean_obj_tag(v_x_1717_) == 1 {
            let mut v_k_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1720_);
            v_k_1724_ = crate::leanh::lean_ctor_get(v_x_1716_, 0);
            crate::leanh::lean_inc(v_k_1724_);
            v_v_1725_ = crate::leanh::lean_ctor_get(v_x_1716_, 1);
            crate::leanh::lean_inc(v_v_1725_);
            v_p_1726_ = crate::leanh::lean_ctor_get(v_x_1716_, 2);
            crate::leanh::lean_inc(v_p_1726_);
            crate::leanh::lean_dec_ref_known(v_x_1716_, 3);
            v_k_1727_ = crate::leanh::lean_ctor_get(v_x_1717_, 0);
            crate::leanh::lean_inc(v_k_1727_);
            v_v_1728_ = crate::leanh::lean_ctor_get(v_x_1717_, 1);
            crate::leanh::lean_inc(v_v_1728_);
            v_p_1729_ = crate::leanh::lean_ctor_get(v_x_1717_, 2);
            crate::leanh::lean_inc(v_p_1729_);
            crate::leanh::lean_dec_ref_known(v_x_1717_, 3);
            v___x_1730_ = crate::leanh::lean_apply_6(
                v_h__2_1719_,
                v_k_1724_,
                v_v_1725_,
                v_p_1726_,
                v_k_1727_,
                v_v_1728_,
                v_p_1729_,
            );
            return v___x_1730_;
        } else {
            let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1719_);
            v___x_1731_ = crate::leanh::lean_apply_4(
                v_h__3_1720_,
                v_x_1716_,
                v_x_1717_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1731_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(
    mut v_motive_1732_: *mut crate::leanh::LeanObject,
    mut v_x_1733_: *mut crate::leanh::LeanObject,
    mut v_x_1734_: *mut crate::leanh::LeanObject,
    mut v_h__1_1735_: *mut crate::leanh::LeanObject,
    mut v_h__2_1736_: *mut crate::leanh::LeanObject,
    mut v_h__3_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1733_) == 0 {
        crate::leanh::lean_dec(v_h__2_1736_);
        if crate::leanh::lean_obj_tag(v_x_1734_) == 0 {
            let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1737_);
            v___x_1738_ = crate::leanh::lean_box(0);
            v___x_1739_ = crate::leanh::lean_apply_1(v_h__1_1735_, v___x_1738_);
            return v___x_1739_;
        } else {
            let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1735_);
            v___x_1740_ = crate::leanh::lean_apply_4(
                v_h__3_1737_,
                v_x_1733_,
                v_x_1734_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1740_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_1735_);
        if crate::leanh::lean_obj_tag(v_x_1734_) == 1 {
            let mut v_k_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1737_);
            v_k_1741_ = crate::leanh::lean_ctor_get(v_x_1733_, 0);
            crate::leanh::lean_inc(v_k_1741_);
            v_v_1742_ = crate::leanh::lean_ctor_get(v_x_1733_, 1);
            crate::leanh::lean_inc(v_v_1742_);
            v_p_1743_ = crate::leanh::lean_ctor_get(v_x_1733_, 2);
            crate::leanh::lean_inc(v_p_1743_);
            crate::leanh::lean_dec_ref_known(v_x_1733_, 3);
            v_k_1744_ = crate::leanh::lean_ctor_get(v_x_1734_, 0);
            crate::leanh::lean_inc(v_k_1744_);
            v_v_1745_ = crate::leanh::lean_ctor_get(v_x_1734_, 1);
            crate::leanh::lean_inc(v_v_1745_);
            v_p_1746_ = crate::leanh::lean_ctor_get(v_x_1734_, 2);
            crate::leanh::lean_inc(v_p_1746_);
            crate::leanh::lean_dec_ref_known(v_x_1734_, 3);
            v___x_1747_ = crate::leanh::lean_apply_6(
                v_h__2_1736_,
                v_k_1741_,
                v_v_1742_,
                v_p_1743_,
                v_k_1744_,
                v_v_1745_,
                v_p_1746_,
            );
            return v___x_1747_;
        } else {
            let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1736_);
            v___x_1748_ = crate::leanh::lean_apply_4(
                v_h__3_1737_,
                v_x_1733_,
                v_x_1734_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1748_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_instReprPoly_repr(
    mut v_x_1758_: *mut crate::leanh::LeanObject,
    mut v_prec_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1758_) == 0 {
                    v___x_1767_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1768_ = lean_nat_dec_le(v___x_1767_, v_prec_1759_);
                    if v___x_1768_ == 0 {
                        v___x_1769_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                        );
                        v___y_1761_ = v___x_1769_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1770_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                        );
                        v___y_1761_ = v___x_1770_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_1771_ = crate::leanh::lean_ctor_get(v_x_1758_, 0);
                    crate::leanh::lean_inc(v_k_1771_);
                    v_v_1772_ = crate::leanh::lean_ctor_get(v_x_1758_, 1);
                    crate::leanh::lean_inc(v_v_1772_);
                    v_p_1773_ = crate::leanh::lean_ctor_get(v_x_1758_, 2);
                    crate::leanh::lean_inc(v_p_1773_);
                    crate::leanh::lean_dec_ref_known(v_x_1758_, 3);
                    v___x_1774_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1803_ = lean_nat_dec_le(v___x_1774_, v_prec_1759_);
                    if v___x_1803_ == 0 {
                        v___x_1804_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2,
                        );
                        v___y_1793_ = v___x_1804_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1805_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                            ),
                            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                        );
                        v___y_1793_ = v___x_1805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1762_ = l_Lean_Grind_Linarith_instReprPoly_repr___closed__1;
                crate::leanh::lean_inc(v___y_1761_);
                v___x_1763_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1763_, 0, v___y_1761_);
                crate::leanh::lean_ctor_set(v___x_1763_, 1, v___x_1762_);
                v___x_1764_ = 0;
                v___x_1765_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1765_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1764_,
                );
                v___x_1766_ = l_Repr_addAppParen(v___x_1765_, v_prec_1759_);
                return v___x_1766_;
            }
            2 => {
                crate::leanh::lean_inc(v___y_1778_);
                v___x_1780_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1780_, 0, v___y_1778_);
                crate::leanh::lean_ctor_set(v___x_1780_, 1, v___y_1779_);
                crate::leanh::lean_inc_n(v___y_1776_, 2);
                v___x_1781_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1781_, 0, v___x_1780_);
                crate::leanh::lean_ctor_set(v___x_1781_, 1, v___y_1776_);
                v___x_1782_ = l_Nat_reprFast(v_v_1772_);
                v___x_1783_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1782_);
                v___x_1784_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                v___x_1785_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1785_, 0, v___x_1784_);
                crate::leanh::lean_ctor_set(v___x_1785_, 1, v___y_1776_);
                v___x_1786_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_p_1773_, v___x_1774_);
                v___x_1787_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1785_);
                crate::leanh::lean_ctor_set(v___x_1787_, 1, v___x_1786_);
                crate::leanh::lean_inc(v___y_1777_);
                v___x_1788_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1788_, 0, v___y_1777_);
                crate::leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = 0;
                v___x_1790_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1790_, 0, v___x_1788_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1789_,
                );
                v___x_1791_ = l_Repr_addAppParen(v___x_1790_, v_prec_1759_);
                return v___x_1791_;
            }
            3 => {
                v___x_1794_ = crate::leanh::lean_box(1);
                v___x_1795_ = l_Lean_Grind_Linarith_instReprPoly_repr___closed__4;
                v___x_1796_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                v___x_1797_ = lean_int_dec_lt(v_k_1771_, v___x_1796_);
                if v___x_1797_ == 0 {
                    v___x_1798_ = l_Int_repr(v_k_1771_);
                    crate::leanh::lean_dec(v_k_1771_);
                    v___x_1799_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1799_, 0, v___x_1798_);
                    v___y_1776_ = v___x_1794_;
                    v___y_1777_ = v___y_1793_;
                    v___y_1778_ = v___x_1795_;
                    v___y_1779_ = v___x_1799_;
                    state = 2;
                    continue;
                } else {
                    v___x_1800_ = l_Int_repr(v_k_1771_);
                    crate::leanh::lean_dec(v_k_1771_);
                    v___x_1801_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
                    v___x_1802_ = l_Repr_addAppParen(v___x_1801_, v___x_1774_);
                    v___y_1776_ = v___x_1794_;
                    v___y_1777_ = v___y_1793_;
                    v___y_1778_ = v___x_1795_;
                    v___y_1779_ = v___x_1802_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_instReprPoly_repr___boxed(
    mut v_x_1806_: *mut crate::leanh::LeanObject,
    mut v_prec_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1808_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_x_1806_, v_prec_1807_);
    crate::leanh::lean_dec(v_prec_1807_);
    return v_res_1808_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote___redArg(
    mut v_inst_1811_: *mut crate::leanh::LeanObject,
    mut v_ctx_1812_: *mut crate::leanh::LeanObject,
    mut v_p_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1811_);
    v_toAddCommMonoid_1815_ = crate::leanh::lean_ctor_get(v___x_1814_, 0);
    crate::leanh::lean_inc_ref(v_toAddCommMonoid_1815_);
    crate::leanh::lean_dec_ref(v___x_1814_);
    if crate::leanh::lean_obj_tag(v_p_1813_) == 0 {
        let mut v_toZero_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1811_);
        v_toZero_1816_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1815_, 0);
        crate::leanh::lean_inc(v_toZero_1816_);
        crate::leanh::lean_dec_ref(v_toAddCommMonoid_1815_);
        return v_toZero_1816_;
    } else {
        let mut v_toAdd_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zsmul_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toAdd_1817_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1815_, 1);
        crate::leanh::lean_inc(v_toAdd_1817_);
        crate::leanh::lean_dec_ref(v_toAddCommMonoid_1815_);
        v_zsmul_1818_ = crate::leanh::lean_ctor_get(v_inst_1811_, 2);
        v_k_1819_ = crate::leanh::lean_ctor_get(v_p_1813_, 0);
        crate::leanh::lean_inc(v_k_1819_);
        v_v_1820_ = crate::leanh::lean_ctor_get(v_p_1813_, 1);
        crate::leanh::lean_inc(v_v_1820_);
        v_p_1821_ = crate::leanh::lean_ctor_get(v_p_1813_, 2);
        crate::leanh::lean_inc(v_p_1821_);
        crate::leanh::lean_dec_ref_known(v_p_1813_, 3);
        v___x_1822_ = l_Lean_RArray_getImpl___redArg(v_ctx_1812_, v_v_1820_);
        crate::leanh::lean_dec(v_v_1820_);
        crate::leanh::lean_inc(v_zsmul_1818_);
        v___x_1823_ = crate::leanh::lean_apply_2(v_zsmul_1818_, v_k_1819_, v___x_1822_);
        v___x_1824_ =
            l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_1811_, v_ctx_1812_, v_p_1821_);
        v___x_1825_ = crate::leanh::lean_apply_2(v_toAdd_1817_, v___x_1823_, v___x_1824_);
        return v___x_1825_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(
    mut v_inst_1826_: *mut crate::leanh::LeanObject,
    mut v_ctx_1827_: *mut crate::leanh::LeanObject,
    mut v_p_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_1826_, v_ctx_1827_, v_p_1828_);
    crate::leanh::lean_dec_ref(v_ctx_1827_);
    return v_res_1829_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote(
    mut v_00_u03b1_1830_: *mut crate::leanh::LeanObject,
    mut v_inst_1831_: *mut crate::leanh::LeanObject,
    mut v_ctx_1832_: *mut crate::leanh::LeanObject,
    mut v_p_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_1831_, v_ctx_1832_, v_p_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote___boxed(
    mut v_00_u03b1_1835_: *mut crate::leanh::LeanObject,
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_ctx_1837_: *mut crate::leanh::LeanObject,
    mut v_p_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ =
        l_Lean_Grind_Linarith_Poly_denote(v_00_u03b1_1835_, v_inst_1836_, v_ctx_1837_, v_p_1838_);
    crate::leanh::lean_dec_ref(v_ctx_1837_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
    mut v_inst_1840_: *mut crate::leanh::LeanObject,
    mut v_ctx_1841_: *mut crate::leanh::LeanObject,
    mut v_r_1842_: *mut crate::leanh::LeanObject,
    mut v_p_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmul_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1844_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1840_);
                v_toAddCommMonoid_1845_ = crate::leanh::lean_ctor_get(v___x_1844_, 0);
                crate::leanh::lean_inc_ref(v_toAddCommMonoid_1845_);
                crate::leanh::lean_dec_ref(v___x_1844_);
                if crate::leanh::lean_obj_tag(v_p_1843_) == 0 {
                    crate::leanh::lean_dec_ref(v_toAddCommMonoid_1845_);
                    crate::leanh::lean_dec_ref(v_inst_1840_);
                    return v_r_1842_;
                } else {
                    v_toAdd_1846_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1845_, 1);
                    crate::leanh::lean_inc(v_toAdd_1846_);
                    crate::leanh::lean_dec_ref(v_toAddCommMonoid_1845_);
                    v_zsmul_1847_ = crate::leanh::lean_ctor_get(v_inst_1840_, 2);
                    v_k_1848_ = crate::leanh::lean_ctor_get(v_p_1843_, 0);
                    crate::leanh::lean_inc(v_k_1848_);
                    v_v_1849_ = crate::leanh::lean_ctor_get(v_p_1843_, 1);
                    crate::leanh::lean_inc(v_v_1849_);
                    v_p_1850_ = crate::leanh::lean_ctor_get(v_p_1843_, 2);
                    crate::leanh::lean_inc(v_p_1850_);
                    crate::leanh::lean_dec_ref_known(v_p_1843_, 3);
                    v___x_1851_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
                    );
                    v___x_1852_ = lean_int_dec_eq(v_k_1848_, v___x_1851_);
                    if v___x_1852_ == 0 {
                        v___x_1853_ = l_Lean_RArray_getImpl___redArg(v_ctx_1841_, v_v_1849_);
                        crate::leanh::lean_dec(v_v_1849_);
                        crate::leanh::lean_inc(v_zsmul_1847_);
                        v___x_1854_ =
                            crate::leanh::lean_apply_2(v_zsmul_1847_, v_k_1848_, v___x_1853_);
                        v___x_1855_ =
                            crate::leanh::lean_apply_2(v_toAdd_1846_, v_r_1842_, v___x_1854_);
                        v_r_1842_ = v___x_1855_;
                        v_p_1843_ = v_p_1850_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_1848_);
                        v___x_1857_ = l_Lean_RArray_getImpl___redArg(v_ctx_1841_, v_v_1849_);
                        crate::leanh::lean_dec(v_v_1849_);
                        v___x_1858_ =
                            crate::leanh::lean_apply_2(v_toAdd_1846_, v_r_1842_, v___x_1857_);
                        v_r_1842_ = v___x_1858_;
                        v_p_1843_ = v_p_1850_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg___boxed(
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
    mut v_ctx_1861_: *mut crate::leanh::LeanObject,
    mut v_r_1862_: *mut crate::leanh::LeanObject,
    mut v_p_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1864_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
        v_inst_1860_,
        v_ctx_1861_,
        v_r_1862_,
        v_p_1863_,
    );
    crate::leanh::lean_dec_ref(v_ctx_1861_);
    return v_res_1864_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go(
    mut v_00_u03b1_1865_: *mut crate::leanh::LeanObject,
    mut v_inst_1866_: *mut crate::leanh::LeanObject,
    mut v_ctx_1867_: *mut crate::leanh::LeanObject,
    mut v_r_1868_: *mut crate::leanh::LeanObject,
    mut v_p_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
        v_inst_1866_,
        v_ctx_1867_,
        v_r_1868_,
        v_p_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(
    mut v_00_u03b1_1871_: *mut crate::leanh::LeanObject,
    mut v_inst_1872_: *mut crate::leanh::LeanObject,
    mut v_ctx_1873_: *mut crate::leanh::LeanObject,
    mut v_r_1874_: *mut crate::leanh::LeanObject,
    mut v_p_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l_Lean_Grind_Linarith_Poly_denote_x27_go(
        v_00_u03b1_1871_,
        v_inst_1872_,
        v_ctx_1873_,
        v_r_1874_,
        v_p_1875_,
    );
    crate::leanh::lean_dec_ref(v_ctx_1873_);
    return v_res_1876_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27___redArg(
    mut v_inst_1877_: *mut crate::leanh::LeanObject,
    mut v_ctx_1878_: *mut crate::leanh::LeanObject,
    mut v_p_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1877_);
    v_toAddCommMonoid_1881_ = crate::leanh::lean_ctor_get(v___x_1880_, 0);
    crate::leanh::lean_inc_ref(v_toAddCommMonoid_1881_);
    crate::leanh::lean_dec_ref(v___x_1880_);
    if crate::leanh::lean_obj_tag(v_p_1879_) == 0 {
        let mut v_toZero_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1877_);
        v_toZero_1882_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1881_, 0);
        crate::leanh::lean_inc(v_toZero_1882_);
        crate::leanh::lean_dec_ref(v_toAddCommMonoid_1881_);
        return v_toZero_1882_;
    } else {
        let mut v_zsmul_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: u8 = 0;
        crate::leanh::lean_dec_ref(v_toAddCommMonoid_1881_);
        v_zsmul_1883_ = crate::leanh::lean_ctor_get(v_inst_1877_, 2);
        v_k_1884_ = crate::leanh::lean_ctor_get(v_p_1879_, 0);
        crate::leanh::lean_inc(v_k_1884_);
        v_v_1885_ = crate::leanh::lean_ctor_get(v_p_1879_, 1);
        crate::leanh::lean_inc(v_v_1885_);
        v_p_1886_ = crate::leanh::lean_ctor_get(v_p_1879_, 2);
        crate::leanh::lean_inc(v_p_1886_);
        crate::leanh::lean_dec_ref_known(v_p_1879_, 3);
        v___x_1887_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1888_ = lean_int_dec_eq(v_k_1884_, v___x_1887_);
        if v___x_1888_ == 0 {
            let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1889_ = l_Lean_RArray_getImpl___redArg(v_ctx_1878_, v_v_1885_);
            crate::leanh::lean_dec(v_v_1885_);
            crate::leanh::lean_inc(v_zsmul_1883_);
            v___x_1890_ = crate::leanh::lean_apply_2(v_zsmul_1883_, v_k_1884_, v___x_1889_);
            v___x_1891_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
                v_inst_1877_,
                v_ctx_1878_,
                v___x_1890_,
                v_p_1886_,
            );
            return v___x_1891_;
        } else {
            let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_1884_);
            v___x_1892_ = l_Lean_RArray_getImpl___redArg(v_ctx_1878_, v_v_1885_);
            crate::leanh::lean_dec(v_v_1885_);
            v___x_1893_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
                v_inst_1877_,
                v_ctx_1878_,
                v___x_1892_,
                v_p_1886_,
            );
            return v___x_1893_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27___redArg___boxed(
    mut v_inst_1894_: *mut crate::leanh::LeanObject,
    mut v_ctx_1895_: *mut crate::leanh::LeanObject,
    mut v_p_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ =
        l_Lean_Grind_Linarith_Poly_denote_x27___redArg(v_inst_1894_, v_ctx_1895_, v_p_1896_);
    crate::leanh::lean_dec_ref(v_ctx_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27(
    mut v_00_u03b1_1898_: *mut crate::leanh::LeanObject,
    mut v_inst_1899_: *mut crate::leanh::LeanObject,
    mut v_ctx_1900_: *mut crate::leanh::LeanObject,
    mut v_p_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1899_);
    v_toAddCommMonoid_1903_ = crate::leanh::lean_ctor_get(v___x_1902_, 0);
    crate::leanh::lean_inc_ref(v_toAddCommMonoid_1903_);
    crate::leanh::lean_dec_ref(v___x_1902_);
    if crate::leanh::lean_obj_tag(v_p_1901_) == 0 {
        let mut v_toZero_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1899_);
        v_toZero_1904_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1903_, 0);
        crate::leanh::lean_inc(v_toZero_1904_);
        crate::leanh::lean_dec_ref(v_toAddCommMonoid_1903_);
        return v_toZero_1904_;
    } else {
        let mut v_zsmul_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: u8 = 0;
        crate::leanh::lean_dec_ref(v_toAddCommMonoid_1903_);
        v_zsmul_1905_ = crate::leanh::lean_ctor_get(v_inst_1899_, 2);
        v_k_1906_ = crate::leanh::lean_ctor_get(v_p_1901_, 0);
        crate::leanh::lean_inc(v_k_1906_);
        v_v_1907_ = crate::leanh::lean_ctor_get(v_p_1901_, 1);
        crate::leanh::lean_inc(v_v_1907_);
        v_p_1908_ = crate::leanh::lean_ctor_get(v_p_1901_, 2);
        crate::leanh::lean_inc(v_p_1908_);
        crate::leanh::lean_dec_ref_known(v_p_1901_, 3);
        v___x_1909_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1910_ = lean_int_dec_eq(v_k_1906_, v___x_1909_);
        if v___x_1910_ == 0 {
            let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1911_ = l_Lean_RArray_getImpl___redArg(v_ctx_1900_, v_v_1907_);
            crate::leanh::lean_dec(v_v_1907_);
            crate::leanh::lean_inc(v_zsmul_1905_);
            v___x_1912_ = crate::leanh::lean_apply_2(v_zsmul_1905_, v_k_1906_, v___x_1911_);
            v___x_1913_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
                v_inst_1899_,
                v_ctx_1900_,
                v___x_1912_,
                v_p_1908_,
            );
            return v___x_1913_;
        } else {
            let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_1906_);
            v___x_1914_ = l_Lean_RArray_getImpl___redArg(v_ctx_1900_, v_v_1907_);
            crate::leanh::lean_dec(v_v_1907_);
            v___x_1915_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
                v_inst_1899_,
                v_ctx_1900_,
                v___x_1914_,
                v_p_1908_,
            );
            return v___x_1915_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27___boxed(
    mut v_00_u03b1_1916_: *mut crate::leanh::LeanObject,
    mut v_inst_1917_: *mut crate::leanh::LeanObject,
    mut v_ctx_1918_: *mut crate::leanh::LeanObject,
    mut v_p_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Grind_Linarith_Poly_denote_x27(
        v_00_u03b1_1916_,
        v_inst_1917_,
        v_ctx_1918_,
        v_p_1919_,
    );
    crate::leanh::lean_dec_ref(v_ctx_1918_);
    return v_res_1920_;
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(
    mut v_p_1921_: *mut crate::leanh::LeanObject,
    mut v_h__1_1922_: *mut crate::leanh::LeanObject,
    mut v_h__2_1923_: *mut crate::leanh::LeanObject,
    mut v_h__3_1924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1921_) == 0 {
        let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1924_);
        crate::leanh::lean_dec(v_h__2_1923_);
        v___x_1925_ = crate::leanh::lean_box(0);
        v___x_1926_ = crate::leanh::lean_apply_1(v_h__1_1922_, v___x_1925_);
        return v___x_1926_;
    } else {
        let mut v_k_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_1922_);
        v_k_1927_ = crate::leanh::lean_ctor_get(v_p_1921_, 0);
        crate::leanh::lean_inc(v_k_1927_);
        v_v_1928_ = crate::leanh::lean_ctor_get(v_p_1921_, 1);
        crate::leanh::lean_inc(v_v_1928_);
        v_p_1929_ = crate::leanh::lean_ctor_get(v_p_1921_, 2);
        crate::leanh::lean_inc(v_p_1929_);
        crate::leanh::lean_dec_ref_known(v_p_1921_, 3);
        v___x_1930_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1931_ = lean_int_dec_eq(v_k_1927_, v___x_1930_);
        if v___x_1931_ == 0 {
            let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1923_);
            v___x_1932_ = crate::leanh::lean_apply_4(
                v_h__3_1924_,
                v_k_1927_,
                v_v_1928_,
                v_p_1929_,
                crate::leanh::lean_box(0),
            );
            return v___x_1932_;
        } else {
            let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_1927_);
            crate::leanh::lean_dec(v_h__3_1924_);
            v___x_1933_ = crate::leanh::lean_apply_2(v_h__2_1923_, v_v_1928_, v_p_1929_);
            return v___x_1933_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(
    mut v_motive_1934_: *mut crate::leanh::LeanObject,
    mut v_p_1935_: *mut crate::leanh::LeanObject,
    mut v_h__1_1936_: *mut crate::leanh::LeanObject,
    mut v_h__2_1937_: *mut crate::leanh::LeanObject,
    mut v_h__3_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1935_) == 0 {
        let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1938_);
        crate::leanh::lean_dec(v_h__2_1937_);
        v___x_1939_ = crate::leanh::lean_box(0);
        v___x_1940_ = crate::leanh::lean_apply_1(v_h__1_1936_, v___x_1939_);
        return v___x_1940_;
    } else {
        let mut v_k_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_1936_);
        v_k_1941_ = crate::leanh::lean_ctor_get(v_p_1935_, 0);
        crate::leanh::lean_inc(v_k_1941_);
        v_v_1942_ = crate::leanh::lean_ctor_get(v_p_1935_, 1);
        crate::leanh::lean_inc(v_v_1942_);
        v_p_1943_ = crate::leanh::lean_ctor_get(v_p_1935_, 2);
        crate::leanh::lean_inc(v_p_1943_);
        crate::leanh::lean_dec_ref_known(v_p_1935_, 3);
        v___x_1944_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1945_ = lean_int_dec_eq(v_k_1941_, v___x_1944_);
        if v___x_1945_ == 0 {
            let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1937_);
            v___x_1946_ = crate::leanh::lean_apply_4(
                v_h__3_1938_,
                v_k_1941_,
                v_v_1942_,
                v_p_1943_,
                crate::leanh::lean_box(0),
            );
            return v___x_1946_;
        } else {
            let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_1941_);
            crate::leanh::lean_dec(v_h__3_1938_);
            v___x_1947_ = crate::leanh::lean_apply_2(v_h__2_1937_, v_v_1942_, v_p_1943_);
            return v___x_1947_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_coeff(
    mut v_p_1948_: *mut crate::leanh::LeanObject,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1948_) == 0 {
                    v___x_1950_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__22
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                    );
                    return v___x_1950_;
                } else {
                    v_k_1951_ = crate::leanh::lean_ctor_get(v_p_1948_, 0);
                    v_v_1952_ = crate::leanh::lean_ctor_get(v_p_1948_, 1);
                    v_p_1953_ = crate::leanh::lean_ctor_get(v_p_1948_, 2);
                    v___x_1954_ = lean_nat_dec_eq(v_x_1949_, v_v_1952_);
                    if v___x_1954_ == 0 {
                        v_p_1948_ = v_p_1953_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_1951_);
                        return v_k_1951_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_coeff___boxed(
    mut v_p_1956_: *mut crate::leanh::LeanObject,
    mut v_x_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1958_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_1956_, v_x_1957_);
    crate::leanh::lean_dec(v_x_1957_);
    crate::leanh::lean_dec(v_p_1956_);
    return v_res_1958_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_insert(
    mut v_k_1959_: *mut crate::leanh::LeanObject,
    mut v_v_1960_: *mut crate::leanh::LeanObject,
    mut v_p_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_unused_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1961_) == 0 {
                    v___x_1962_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1962_, 0, v_k_1959_);
                    crate::leanh::lean_ctor_set(v___x_1962_, 1, v_v_1960_);
                    crate::leanh::lean_ctor_set(v___x_1962_, 2, v_p_1961_);
                    return v___x_1962_;
                } else {
                    v_k_1963_ = crate::leanh::lean_ctor_get(v_p_1961_, 0);
                    v_v_1964_ = crate::leanh::lean_ctor_get(v_p_1961_, 1);
                    v_p_1965_ = crate::leanh::lean_ctor_get(v_p_1961_, 2);
                    v___x_1966_ = l_Nat_blt(v_v_1964_, v_v_1960_);
                    if v___x_1966_ == 0 {
                        crate::leanh::lean_inc(v_p_1965_);
                        crate::leanh::lean_inc(v_v_1964_);
                        crate::leanh::lean_inc(v_k_1963_);
                        v_isSharedCheck_1981_ = (!crate::leanh::lean_is_exclusive(v_p_1961_)) as u8;
                        if v_isSharedCheck_1981_ == 0 {
                            v_unused_1982_ = crate::leanh::lean_ctor_get(v_p_1961_, 2);
                            crate::leanh::lean_dec(v_unused_1982_);
                            v_unused_1983_ = crate::leanh::lean_ctor_get(v_p_1961_, 1);
                            crate::leanh::lean_dec(v_unused_1983_);
                            v_unused_1984_ = crate::leanh::lean_ctor_get(v_p_1961_, 0);
                            crate::leanh::lean_dec(v_unused_1984_);
                            v___x_1968_ = v_p_1961_;
                            v_isShared_1969_ = v_isSharedCheck_1981_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_p_1961_);
                            v___x_1968_ = crate::leanh::lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_1981_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1985_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1985_, 0, v_k_1959_);
                        crate::leanh::lean_ctor_set(v___x_1985_, 1, v_v_1960_);
                        crate::leanh::lean_ctor_set(v___x_1985_, 2, v_p_1961_);
                        return v___x_1985_;
                    }
                }
            }
            1 => {
                v___x_1970_ = lean_nat_dec_eq(v_v_1960_, v_v_1964_);
                if v___x_1970_ == 0 {
                    v___x_1971_ =
                        l_Lean_Grind_Linarith_Poly_insert(v_k_1959_, v_v_1960_, v_p_1965_);
                    if v_isShared_1969_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1968_, 2, v___x_1971_);
                        v___x_1973_ = v___x_1968_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1974_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_k_1963_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_v_1964_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 2, v___x_1971_);
                        v___x_1973_ = v_reuseFailAlloc_1974_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_v_1960_);
                    v___x_1975_ = lean_int_add(v_k_1959_, v_k_1963_);
                    crate::leanh::lean_dec(v_k_1963_);
                    crate::leanh::lean_dec(v_k_1959_);
                    v___x_1976_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__22
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                    );
                    v___x_1977_ = lean_int_dec_eq(v___x_1975_, v___x_1976_);
                    if v___x_1977_ == 0 {
                        if v_isShared_1969_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_1975_);
                            v___x_1979_ = v___x_1968_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1980_ =
                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1975_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_v_1964_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_p_1965_);
                            v___x_1979_ = v_reuseFailAlloc_1980_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1975_);
                        crate::leanh::lean_del_object(v___x_1968_);
                        crate::leanh::lean_dec(v_v_1964_);
                        return v_p_1965_;
                    }
                }
            }
            2 => {
                return v___x_1973_;
            }
            3 => {
                return v___x_1979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_norm(
    mut v_p_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1986_) == 0 {
        return v_p_1986_;
    } else {
        let mut v_k_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1987_ = crate::leanh::lean_ctor_get(v_p_1986_, 0);
        crate::leanh::lean_inc(v_k_1987_);
        v_v_1988_ = crate::leanh::lean_ctor_get(v_p_1986_, 1);
        crate::leanh::lean_inc(v_v_1988_);
        v_p_1989_ = crate::leanh::lean_ctor_get(v_p_1986_, 2);
        crate::leanh::lean_inc(v_p_1989_);
        crate::leanh::lean_dec_ref_known(v_p_1986_, 3);
        v___x_1990_ = l_Lean_Grind_Linarith_Poly_norm(v_p_1989_);
        v___x_1991_ = l_Lean_Grind_Linarith_Poly_insert(v_k_1987_, v_v_1988_, v___x_1990_);
        return v___x_1991_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_append(
    mut v_p_u2081_1992_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_1992_) == 0 {
                    crate::leanh::lean_inc(v_p_u2082_1993_);
                    return v_p_u2082_1993_;
                } else {
                    v_k_1994_ = crate::leanh::lean_ctor_get(v_p_u2081_1992_, 0);
                    v_v_1995_ = crate::leanh::lean_ctor_get(v_p_u2081_1992_, 1);
                    v_p_1996_ = crate::leanh::lean_ctor_get(v_p_u2081_1992_, 2);
                    v_isSharedCheck_2004_ =
                        (!crate::leanh::lean_is_exclusive(v_p_u2081_1992_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v___x_1998_ = v_p_u2081_1992_;
                        v_isShared_1999_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_1996_);
                        crate::leanh::lean_inc(v_v_1995_);
                        crate::leanh::lean_inc(v_k_1994_);
                        crate::leanh::lean_dec(v_p_u2081_1992_);
                        v___x_1998_ = crate::leanh::lean_box(0);
                        v_isShared_1999_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2000_ = l_Lean_Grind_Linarith_Poly_append(v_p_1996_, v_p_u2082_1993_);
                if v_isShared_1999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1998_, 2, v___x_2000_);
                    v___x_2002_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_k_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_v_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 2, v___x_2000_);
                    v___x_2002_ = v_reuseFailAlloc_2003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_append___boxed(
    mut v_p_u2081_2005_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Grind_Linarith_Poly_append(v_p_u2081_2005_, v_p_u2082_2006_);
    crate::leanh::lean_dec(v_p_u2082_2006_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_combine(
    mut v_p_u2081_2008_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_unused_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2031_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_unused_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v_a_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2051_: u8 = 0;
    let mut v_unused_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_2008_) == 0 {
                    return v_p_u2082_2009_;
                } else {
                    if crate::leanh::lean_obj_tag(v_p_u2082_2009_) == 0 {
                        return v_p_u2081_2008_;
                    } else {
                        v_k_2010_ = crate::leanh::lean_ctor_get(v_p_u2081_2008_, 0);
                        v_v_2011_ = crate::leanh::lean_ctor_get(v_p_u2081_2008_, 1);
                        v_p_2012_ = crate::leanh::lean_ctor_get(v_p_u2081_2008_, 2);
                        v_k_2013_ = crate::leanh::lean_ctor_get(v_p_u2082_2009_, 0);
                        v_v_2014_ = crate::leanh::lean_ctor_get(v_p_u2082_2009_, 1);
                        v_p_2015_ = crate::leanh::lean_ctor_get(v_p_u2082_2009_, 2);
                        v___x_2016_ = lean_nat_dec_eq(v_v_2011_, v_v_2014_);
                        if v___x_2016_ == 0 {
                            v___x_2017_ = l_Nat_blt(v_v_2014_, v_v_2011_);
                            if v___x_2017_ == 0 {
                                crate::leanh::lean_inc(v_p_2015_);
                                crate::leanh::lean_inc(v_v_2014_);
                                crate::leanh::lean_inc(v_k_2013_);
                                v_isSharedCheck_2025_ =
                                    (!crate::leanh::lean_is_exclusive(v_p_u2082_2009_)) as u8;
                                if v_isSharedCheck_2025_ == 0 {
                                    v_unused_2026_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_2009_, 2);
                                    crate::leanh::lean_dec(v_unused_2026_);
                                    v_unused_2027_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_2009_, 1);
                                    crate::leanh::lean_dec(v_unused_2027_);
                                    v_unused_2028_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_2009_, 0);
                                    crate::leanh::lean_dec(v_unused_2028_);
                                    v___x_2019_ = v_p_u2082_2009_;
                                    v_isShared_2020_ = v_isSharedCheck_2025_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_p_u2082_2009_);
                                    v___x_2019_ = crate::leanh::lean_box(0);
                                    v_isShared_2020_ = v_isSharedCheck_2025_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_p_2012_);
                                crate::leanh::lean_inc(v_v_2011_);
                                crate::leanh::lean_inc(v_k_2010_);
                                v_isSharedCheck_2036_ =
                                    (!crate::leanh::lean_is_exclusive(v_p_u2081_2008_)) as u8;
                                if v_isSharedCheck_2036_ == 0 {
                                    v_unused_2037_ =
                                        crate::leanh::lean_ctor_get(v_p_u2081_2008_, 2);
                                    crate::leanh::lean_dec(v_unused_2037_);
                                    v_unused_2038_ =
                                        crate::leanh::lean_ctor_get(v_p_u2081_2008_, 1);
                                    crate::leanh::lean_dec(v_unused_2038_);
                                    v_unused_2039_ =
                                        crate::leanh::lean_ctor_get(v_p_u2081_2008_, 0);
                                    crate::leanh::lean_dec(v_unused_2039_);
                                    v___x_2030_ = v_p_u2081_2008_;
                                    v_isShared_2031_ = v_isSharedCheck_2036_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_p_u2081_2008_);
                                    v___x_2030_ = crate::leanh::lean_box(0);
                                    v_isShared_2031_ = v_isSharedCheck_2036_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc(v_p_2015_);
                            crate::leanh::lean_inc(v_k_2013_);
                            crate::leanh::lean_inc(v_p_2012_);
                            crate::leanh::lean_inc(v_v_2011_);
                            crate::leanh::lean_inc(v_k_2010_);
                            crate::leanh::lean_dec_ref_known(v_p_u2081_2008_, 3);
                            v_isSharedCheck_2051_ =
                                (!crate::leanh::lean_is_exclusive(v_p_u2082_2009_)) as u8;
                            if v_isSharedCheck_2051_ == 0 {
                                v_unused_2052_ = crate::leanh::lean_ctor_get(v_p_u2082_2009_, 2);
                                crate::leanh::lean_dec(v_unused_2052_);
                                v_unused_2053_ = crate::leanh::lean_ctor_get(v_p_u2082_2009_, 1);
                                crate::leanh::lean_dec(v_unused_2053_);
                                v_unused_2054_ = crate::leanh::lean_ctor_get(v_p_u2082_2009_, 0);
                                crate::leanh::lean_dec(v_unused_2054_);
                                v___x_2041_ = v_p_u2082_2009_;
                                v_isShared_2042_ = v_isSharedCheck_2051_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_p_u2082_2009_);
                                v___x_2041_ = crate::leanh::lean_box(0);
                                v_isShared_2042_ = v_isSharedCheck_2051_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2021_ = l_Lean_Grind_Linarith_Poly_combine(v_p_u2081_2008_, v_p_2015_);
                if v_isShared_2020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2019_, 2, v___x_2021_);
                    v___x_2023_ = v___x_2019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_k_2013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_v_2014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 2, v___x_2021_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2023_;
            }
            3 => {
                v___x_2032_ = l_Lean_Grind_Linarith_Poly_combine(v_p_2012_, v_p_u2082_2009_);
                if v_isShared_2031_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2030_, 2, v___x_2032_);
                    v___x_2034_ = v___x_2030_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_k_2010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_v_2011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 2, v___x_2032_);
                    v___x_2034_ = v_reuseFailAlloc_2035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2034_;
            }
            5 => {
                v_a_2043_ = lean_int_add(v_k_2010_, v_k_2013_);
                crate::leanh::lean_dec(v_k_2013_);
                crate::leanh::lean_dec(v_k_2010_);
                v___x_2044_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                v___x_2045_ = lean_int_dec_eq(v_a_2043_, v___x_2044_);
                if v___x_2045_ == 0 {
                    v___x_2046_ = l_Lean_Grind_Linarith_Poly_combine(v_p_2012_, v_p_2015_);
                    if v_isShared_2042_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2041_, 2, v___x_2046_);
                        crate::leanh::lean_ctor_set(v___x_2041_, 1, v_v_2011_);
                        crate::leanh::lean_ctor_set(v___x_2041_, 0, v_a_2043_);
                        v___x_2048_ = v___x_2041_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_v_2011_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 2, v___x_2046_);
                        v___x_2048_ = v_reuseFailAlloc_2049_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2043_);
                    crate::leanh::lean_del_object(v___x_2041_);
                    crate::leanh::lean_dec(v_v_2011_);
                    v_p_u2081_2008_ = v_p_2012_;
                    v_p_u2082_2009_ = v_p_2015_;
                    state = 0;
                    continue;
                }
            }
            6 => {
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(
    mut v_p_u2081_2055_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2056_: *mut crate::leanh::LeanObject,
    mut v_h__1_2057_: *mut crate::leanh::LeanObject,
    mut v_h__2_2058_: *mut crate::leanh::LeanObject,
    mut v_h__3_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_2055_) == 0 {
        let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_2059_);
        crate::leanh::lean_dec(v_h__2_2058_);
        v___x_2060_ = crate::leanh::lean_apply_1(v_h__1_2057_, v_p_u2082_2056_);
        return v___x_2060_;
    } else {
        crate::leanh::lean_dec(v_h__1_2057_);
        if crate::leanh::lean_obj_tag(v_p_u2082_2056_) == 0 {
            let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2059_);
            v___x_2061_ = crate::leanh::lean_apply_2(
                v_h__2_2058_,
                v_p_u2081_2055_,
                crate::leanh::lean_box(0),
            );
            return v___x_2061_;
        } else {
            let mut v_k_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2058_);
            v_k_2062_ = crate::leanh::lean_ctor_get(v_p_u2081_2055_, 0);
            crate::leanh::lean_inc(v_k_2062_);
            v_v_2063_ = crate::leanh::lean_ctor_get(v_p_u2081_2055_, 1);
            crate::leanh::lean_inc(v_v_2063_);
            v_p_2064_ = crate::leanh::lean_ctor_get(v_p_u2081_2055_, 2);
            crate::leanh::lean_inc(v_p_2064_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2055_, 3);
            v_k_2065_ = crate::leanh::lean_ctor_get(v_p_u2082_2056_, 0);
            crate::leanh::lean_inc(v_k_2065_);
            v_v_2066_ = crate::leanh::lean_ctor_get(v_p_u2082_2056_, 1);
            crate::leanh::lean_inc(v_v_2066_);
            v_p_2067_ = crate::leanh::lean_ctor_get(v_p_u2082_2056_, 2);
            crate::leanh::lean_inc(v_p_2067_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2056_, 3);
            v___x_2068_ = crate::leanh::lean_apply_6(
                v_h__3_2059_,
                v_k_2062_,
                v_v_2063_,
                v_p_2064_,
                v_k_2065_,
                v_v_2066_,
                v_p_2067_,
            );
            return v___x_2068_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(
    mut v_motive_2069_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2070_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2071_: *mut crate::leanh::LeanObject,
    mut v_h__1_2072_: *mut crate::leanh::LeanObject,
    mut v_h__2_2073_: *mut crate::leanh::LeanObject,
    mut v_h__3_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_2070_) == 0 {
        let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_2074_);
        crate::leanh::lean_dec(v_h__2_2073_);
        v___x_2075_ = crate::leanh::lean_apply_1(v_h__1_2072_, v_p_u2082_2071_);
        return v___x_2075_;
    } else {
        crate::leanh::lean_dec(v_h__1_2072_);
        if crate::leanh::lean_obj_tag(v_p_u2082_2071_) == 0 {
            let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2074_);
            v___x_2076_ = crate::leanh::lean_apply_2(
                v_h__2_2073_,
                v_p_u2081_2070_,
                crate::leanh::lean_box(0),
            );
            return v___x_2076_;
        } else {
            let mut v_k_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2073_);
            v_k_2077_ = crate::leanh::lean_ctor_get(v_p_u2081_2070_, 0);
            crate::leanh::lean_inc(v_k_2077_);
            v_v_2078_ = crate::leanh::lean_ctor_get(v_p_u2081_2070_, 1);
            crate::leanh::lean_inc(v_v_2078_);
            v_p_2079_ = crate::leanh::lean_ctor_get(v_p_u2081_2070_, 2);
            crate::leanh::lean_inc(v_p_2079_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2070_, 3);
            v_k_2080_ = crate::leanh::lean_ctor_get(v_p_u2082_2071_, 0);
            crate::leanh::lean_inc(v_k_2080_);
            v_v_2081_ = crate::leanh::lean_ctor_get(v_p_u2082_2071_, 1);
            crate::leanh::lean_inc(v_v_2081_);
            v_p_2082_ = crate::leanh::lean_ctor_get(v_p_u2082_2071_, 2);
            crate::leanh::lean_inc(v_p_2082_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2071_, 3);
            v___x_2083_ = crate::leanh::lean_apply_6(
                v_h__3_2074_,
                v_k_2077_,
                v_v_2078_,
                v_p_2079_,
                v_k_2080_,
                v_v_2081_,
                v_p_2082_,
            );
            return v___x_2083_;
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPoly_x27_go_spec__0(
    mut v_a_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = lean_nat_to_int(v_a_2084_);
    return v___x_2085_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_toPoly_x27_go(
    mut v_coeff_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: u8 = 0;
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_2087_) {
                0 => {
                    crate::leanh::lean_dec(v_coeff_2086_);
                    return v_a_2088_;
                }
                1 => {
                    v_i_2089_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                    crate::leanh::lean_inc(v_i_2089_);
                    crate::leanh::lean_dec_ref_known(v_a_2087_, 1);
                    v___x_2090_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2090_, 0, v_coeff_2086_);
                    crate::leanh::lean_ctor_set(v___x_2090_, 1, v_i_2089_);
                    crate::leanh::lean_ctor_set(v___x_2090_, 2, v_a_2088_);
                    return v___x_2090_;
                }
                2 => {
                    v_a_2091_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                    crate::leanh::lean_inc(v_a_2091_);
                    v_b_2092_ = crate::leanh::lean_ctor_get(v_a_2087_, 1);
                    crate::leanh::lean_inc(v_b_2092_);
                    crate::leanh::lean_dec_ref_known(v_a_2087_, 2);
                    crate::leanh::lean_inc(v_coeff_2086_);
                    v___x_2093_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(
                        v_coeff_2086_,
                        v_b_2092_,
                        v_a_2088_,
                    );
                    v_a_2087_ = v_a_2091_;
                    v_a_2088_ = v___x_2093_;
                    state = 0;
                    continue;
                }
                3 => {
                    v_a_2095_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                    crate::leanh::lean_inc(v_a_2095_);
                    v_b_2096_ = crate::leanh::lean_ctor_get(v_a_2087_, 1);
                    crate::leanh::lean_inc(v_b_2096_);
                    crate::leanh::lean_dec_ref_known(v_a_2087_, 2);
                    v___x_2097_ = lean_int_neg(v_coeff_2086_);
                    v___x_2098_ =
                        l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_2097_, v_b_2096_, v_a_2088_);
                    v_a_2087_ = v_a_2095_;
                    v_a_2088_ = v___x_2098_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_a_2100_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                    crate::leanh::lean_inc(v_a_2100_);
                    crate::leanh::lean_dec_ref_known(v_a_2087_, 1);
                    v___x_2101_ = lean_int_neg(v_coeff_2086_);
                    crate::leanh::lean_dec(v_coeff_2086_);
                    v_coeff_2086_ = v___x_2101_;
                    v_a_2087_ = v_a_2100_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_k_2103_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                    crate::leanh::lean_inc(v_k_2103_);
                    v_a_2104_ = crate::leanh::lean_ctor_get(v_a_2087_, 1);
                    crate::leanh::lean_inc(v_a_2104_);
                    crate::leanh::lean_dec_ref_known(v_a_2087_, 2);
                    v___x_2105_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2106_ = lean_nat_dec_eq(v_k_2103_, v___x_2105_);
                    if v___x_2106_ == 0 {
                        v___x_2107_ = lean_nat_to_int(v_k_2103_);
                        v___x_2108_ = lean_int_mul(v_coeff_2086_, v___x_2107_);
                        crate::leanh::lean_dec(v___x_2107_);
                        crate::leanh::lean_dec(v_coeff_2086_);
                        v_coeff_2086_ = v___x_2108_;
                        v_a_2087_ = v_a_2104_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2104_);
                        crate::leanh::lean_dec(v_k_2103_);
                        crate::leanh::lean_dec(v_coeff_2086_);
                        return v_a_2088_;
                    }
                }
                _ => {
                    v_k_2110_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                    crate::leanh::lean_inc(v_k_2110_);
                    v_a_2111_ = crate::leanh::lean_ctor_get(v_a_2087_, 1);
                    crate::leanh::lean_inc(v_a_2111_);
                    crate::leanh::lean_dec_ref_known(v_a_2087_, 2);
                    v___x_2112_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__22
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                        ),
                        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                    );
                    v___x_2113_ = lean_int_dec_eq(v_k_2110_, v___x_2112_);
                    if v___x_2113_ == 0 {
                        v___x_2114_ = lean_int_mul(v_coeff_2086_, v_k_2110_);
                        crate::leanh::lean_dec(v_k_2110_);
                        crate::leanh::lean_dec(v_coeff_2086_);
                        v_coeff_2086_ = v___x_2114_;
                        v_a_2087_ = v_a_2111_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2111_);
                        crate::leanh::lean_dec(v_k_2110_);
                        crate::leanh::lean_dec(v_coeff_2086_);
                        return v_a_2088_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_toPoly_x27(
    mut v_e_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2118_ = crate::leanh::lean_box(0);
    v___x_2119_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_2117_, v_e_2116_, v___x_2118_);
    return v___x_2119_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_norm(
    mut v_e_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_Grind_Linarith_Expr_toPoly_x27(v_e_2120_);
    v___x_2122_ = l_Lean_Grind_Linarith_Poly_norm(v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul_x27(
    mut v_p_2123_: *mut crate::leanh::LeanObject,
    mut v_k_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_2123_) == 0 {
                    return v_p_2123_;
                } else {
                    v_k_2125_ = crate::leanh::lean_ctor_get(v_p_2123_, 0);
                    v_v_2126_ = crate::leanh::lean_ctor_get(v_p_2123_, 1);
                    v_p_2127_ = crate::leanh::lean_ctor_get(v_p_2123_, 2);
                    v_isSharedCheck_2136_ = (!crate::leanh::lean_is_exclusive(v_p_2123_)) as u8;
                    if v_isSharedCheck_2136_ == 0 {
                        v___x_2129_ = v_p_2123_;
                        v_isShared_2130_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_2127_);
                        crate::leanh::lean_inc(v_v_2126_);
                        crate::leanh::lean_inc(v_k_2125_);
                        crate::leanh::lean_dec(v_p_2123_);
                        v___x_2129_ = crate::leanh::lean_box(0);
                        v_isShared_2130_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2131_ = lean_int_mul(v_k_2124_, v_k_2125_);
                crate::leanh::lean_dec(v_k_2125_);
                v___x_2132_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_2127_, v_k_2124_);
                if v_isShared_2130_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2129_, 2, v___x_2132_);
                    crate::leanh::lean_ctor_set(v___x_2129_, 0, v___x_2131_);
                    v___x_2134_ = v___x_2129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_v_2126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 2, v___x_2132_);
                    v___x_2134_ = v_reuseFailAlloc_2135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul_x27___boxed(
    mut v_p_2137_: *mut crate::leanh::LeanObject,
    mut v_k_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2139_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_2137_, v_k_2138_);
    crate::leanh::lean_dec(v_k_2138_);
    return v_res_2139_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul(
    mut v_p_2140_: *mut crate::leanh::LeanObject,
    mut v_k_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: u8 = 0;
    v___x_2142_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2143_ = lean_int_dec_eq(v_k_2141_, v___x_2142_);
    if v___x_2143_ == 0 {
        let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2144_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_2140_, v_k_2141_);
        return v___x_2144_;
    } else {
        let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_p_2140_);
        v___x_2145_ = crate::leanh::lean_box(0);
        return v___x_2145_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul___boxed(
    mut v_p_2146_: *mut crate::leanh::LeanObject,
    mut v_k_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2148_ = l_Lean_Grind_Linarith_Poly_mul(v_p_2146_, v_k_2147_);
    crate::leanh::lean_dec(v_k_2147_);
    return v_res_2148_;
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(
    mut v_p_2149_: *mut crate::leanh::LeanObject,
    mut v_h__1_2150_: *mut crate::leanh::LeanObject,
    mut v_h__2_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2149_) == 0 {
        let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2151_);
        v___x_2152_ = crate::leanh::lean_box(0);
        v___x_2153_ = crate::leanh::lean_apply_1(v_h__1_2150_, v___x_2152_);
        return v___x_2153_;
    } else {
        let mut v_k_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2150_);
        v_k_2154_ = crate::leanh::lean_ctor_get(v_p_2149_, 0);
        crate::leanh::lean_inc(v_k_2154_);
        v_v_2155_ = crate::leanh::lean_ctor_get(v_p_2149_, 1);
        crate::leanh::lean_inc(v_v_2155_);
        v_p_2156_ = crate::leanh::lean_ctor_get(v_p_2149_, 2);
        crate::leanh::lean_inc(v_p_2156_);
        crate::leanh::lean_dec_ref_known(v_p_2149_, 3);
        v___x_2157_ = crate::leanh::lean_apply_3(v_h__2_2151_, v_k_2154_, v_v_2155_, v_p_2156_);
        return v___x_2157_;
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(
    mut v_motive_2158_: *mut crate::leanh::LeanObject,
    mut v_p_2159_: *mut crate::leanh::LeanObject,
    mut v_h__1_2160_: *mut crate::leanh::LeanObject,
    mut v_h__2_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2159_) == 0 {
        let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2161_);
        v___x_2162_ = crate::leanh::lean_box(0);
        v___x_2163_ = crate::leanh::lean_apply_1(v_h__1_2160_, v___x_2162_);
        return v___x_2163_;
    } else {
        let mut v_k_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2160_);
        v_k_2164_ = crate::leanh::lean_ctor_get(v_p_2159_, 0);
        crate::leanh::lean_inc(v_k_2164_);
        v_v_2165_ = crate::leanh::lean_ctor_get(v_p_2159_, 1);
        crate::leanh::lean_inc(v_v_2165_);
        v_p_2166_ = crate::leanh::lean_ctor_get(v_p_2159_, 2);
        crate::leanh::lean_inc(v_p_2166_);
        crate::leanh::lean_dec_ref_known(v_p_2159_, 3);
        v___x_2167_ = crate::leanh::lean_apply_3(v_h__2_2161_, v_k_2164_, v_v_2165_, v_p_2166_);
        return v___x_2167_;
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(
    mut v_x_2168_: *mut crate::leanh::LeanObject,
    mut v_h__1_2169_: *mut crate::leanh::LeanObject,
    mut v_h__2_2170_: *mut crate::leanh::LeanObject,
    mut v_h__3_2171_: *mut crate::leanh::LeanObject,
    mut v_h__4_2172_: *mut crate::leanh::LeanObject,
    mut v_h__5_2173_: *mut crate::leanh::LeanObject,
    mut v_h__6_2174_: *mut crate::leanh::LeanObject,
    mut v_h__7_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2168_) {
        0 => {
            let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2175_);
            crate::leanh::lean_dec(v_h__6_2174_);
            crate::leanh::lean_dec(v_h__5_2173_);
            crate::leanh::lean_dec(v_h__4_2172_);
            crate::leanh::lean_dec(v_h__3_2171_);
            crate::leanh::lean_dec(v_h__2_2170_);
            v___x_2176_ = crate::leanh::lean_box(0);
            v___x_2177_ = crate::leanh::lean_apply_1(v_h__1_2169_, v___x_2176_);
            return v___x_2177_;
        }
        1 => {
            let mut v_i_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2175_);
            crate::leanh::lean_dec(v_h__6_2174_);
            crate::leanh::lean_dec(v_h__5_2173_);
            crate::leanh::lean_dec(v_h__4_2172_);
            crate::leanh::lean_dec(v_h__3_2171_);
            crate::leanh::lean_dec(v_h__1_2169_);
            v_i_2178_ = crate::leanh::lean_ctor_get(v_x_2168_, 0);
            crate::leanh::lean_inc(v_i_2178_);
            crate::leanh::lean_dec_ref_known(v_x_2168_, 1);
            v___x_2179_ = crate::leanh::lean_apply_1(v_h__2_2170_, v_i_2178_);
            return v___x_2179_;
        }
        2 => {
            let mut v_a_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2175_);
            crate::leanh::lean_dec(v_h__6_2174_);
            crate::leanh::lean_dec(v_h__5_2173_);
            crate::leanh::lean_dec(v_h__4_2172_);
            crate::leanh::lean_dec(v_h__2_2170_);
            crate::leanh::lean_dec(v_h__1_2169_);
            v_a_2180_ = crate::leanh::lean_ctor_get(v_x_2168_, 0);
            crate::leanh::lean_inc(v_a_2180_);
            v_b_2181_ = crate::leanh::lean_ctor_get(v_x_2168_, 1);
            crate::leanh::lean_inc(v_b_2181_);
            crate::leanh::lean_dec_ref_known(v_x_2168_, 2);
            v___x_2182_ = crate::leanh::lean_apply_2(v_h__3_2171_, v_a_2180_, v_b_2181_);
            return v___x_2182_;
        }
        3 => {
            let mut v_a_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2175_);
            crate::leanh::lean_dec(v_h__6_2174_);
            crate::leanh::lean_dec(v_h__5_2173_);
            crate::leanh::lean_dec(v_h__3_2171_);
            crate::leanh::lean_dec(v_h__2_2170_);
            crate::leanh::lean_dec(v_h__1_2169_);
            v_a_2183_ = crate::leanh::lean_ctor_get(v_x_2168_, 0);
            crate::leanh::lean_inc(v_a_2183_);
            v_b_2184_ = crate::leanh::lean_ctor_get(v_x_2168_, 1);
            crate::leanh::lean_inc(v_b_2184_);
            crate::leanh::lean_dec_ref_known(v_x_2168_, 2);
            v___x_2185_ = crate::leanh::lean_apply_2(v_h__4_2172_, v_a_2183_, v_b_2184_);
            return v___x_2185_;
        }
        4 => {
            let mut v_a_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_2174_);
            crate::leanh::lean_dec(v_h__5_2173_);
            crate::leanh::lean_dec(v_h__4_2172_);
            crate::leanh::lean_dec(v_h__3_2171_);
            crate::leanh::lean_dec(v_h__2_2170_);
            crate::leanh::lean_dec(v_h__1_2169_);
            v_a_2186_ = crate::leanh::lean_ctor_get(v_x_2168_, 0);
            crate::leanh::lean_inc(v_a_2186_);
            crate::leanh::lean_dec_ref_known(v_x_2168_, 1);
            v___x_2187_ = crate::leanh::lean_apply_1(v_h__7_2175_, v_a_2186_);
            return v___x_2187_;
        }
        5 => {
            let mut v_k_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2175_);
            crate::leanh::lean_dec(v_h__6_2174_);
            crate::leanh::lean_dec(v_h__4_2172_);
            crate::leanh::lean_dec(v_h__3_2171_);
            crate::leanh::lean_dec(v_h__2_2170_);
            crate::leanh::lean_dec(v_h__1_2169_);
            v_k_2188_ = crate::leanh::lean_ctor_get(v_x_2168_, 0);
            crate::leanh::lean_inc(v_k_2188_);
            v_a_2189_ = crate::leanh::lean_ctor_get(v_x_2168_, 1);
            crate::leanh::lean_inc(v_a_2189_);
            crate::leanh::lean_dec_ref_known(v_x_2168_, 2);
            v___x_2190_ = crate::leanh::lean_apply_2(v_h__5_2173_, v_k_2188_, v_a_2189_);
            return v___x_2190_;
        }
        _ => {
            let mut v_k_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2175_);
            crate::leanh::lean_dec(v_h__5_2173_);
            crate::leanh::lean_dec(v_h__4_2172_);
            crate::leanh::lean_dec(v_h__3_2171_);
            crate::leanh::lean_dec(v_h__2_2170_);
            crate::leanh::lean_dec(v_h__1_2169_);
            v_k_2191_ = crate::leanh::lean_ctor_get(v_x_2168_, 0);
            crate::leanh::lean_inc(v_k_2191_);
            v_a_2192_ = crate::leanh::lean_ctor_get(v_x_2168_, 1);
            crate::leanh::lean_inc(v_a_2192_);
            crate::leanh::lean_dec_ref_known(v_x_2168_, 2);
            v___x_2193_ = crate::leanh::lean_apply_2(v_h__6_2174_, v_k_2191_, v_a_2192_);
            return v___x_2193_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(
    mut v_motive_2194_: *mut crate::leanh::LeanObject,
    mut v_x_2195_: *mut crate::leanh::LeanObject,
    mut v_h__1_2196_: *mut crate::leanh::LeanObject,
    mut v_h__2_2197_: *mut crate::leanh::LeanObject,
    mut v_h__3_2198_: *mut crate::leanh::LeanObject,
    mut v_h__4_2199_: *mut crate::leanh::LeanObject,
    mut v_h__5_2200_: *mut crate::leanh::LeanObject,
    mut v_h__6_2201_: *mut crate::leanh::LeanObject,
    mut v_h__7_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2195_) {
        0 => {
            let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2202_);
            crate::leanh::lean_dec(v_h__6_2201_);
            crate::leanh::lean_dec(v_h__5_2200_);
            crate::leanh::lean_dec(v_h__4_2199_);
            crate::leanh::lean_dec(v_h__3_2198_);
            crate::leanh::lean_dec(v_h__2_2197_);
            v___x_2203_ = crate::leanh::lean_box(0);
            v___x_2204_ = crate::leanh::lean_apply_1(v_h__1_2196_, v___x_2203_);
            return v___x_2204_;
        }
        1 => {
            let mut v_i_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2202_);
            crate::leanh::lean_dec(v_h__6_2201_);
            crate::leanh::lean_dec(v_h__5_2200_);
            crate::leanh::lean_dec(v_h__4_2199_);
            crate::leanh::lean_dec(v_h__3_2198_);
            crate::leanh::lean_dec(v_h__1_2196_);
            v_i_2205_ = crate::leanh::lean_ctor_get(v_x_2195_, 0);
            crate::leanh::lean_inc(v_i_2205_);
            crate::leanh::lean_dec_ref_known(v_x_2195_, 1);
            v___x_2206_ = crate::leanh::lean_apply_1(v_h__2_2197_, v_i_2205_);
            return v___x_2206_;
        }
        2 => {
            let mut v_a_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2202_);
            crate::leanh::lean_dec(v_h__6_2201_);
            crate::leanh::lean_dec(v_h__5_2200_);
            crate::leanh::lean_dec(v_h__4_2199_);
            crate::leanh::lean_dec(v_h__2_2197_);
            crate::leanh::lean_dec(v_h__1_2196_);
            v_a_2207_ = crate::leanh::lean_ctor_get(v_x_2195_, 0);
            crate::leanh::lean_inc(v_a_2207_);
            v_b_2208_ = crate::leanh::lean_ctor_get(v_x_2195_, 1);
            crate::leanh::lean_inc(v_b_2208_);
            crate::leanh::lean_dec_ref_known(v_x_2195_, 2);
            v___x_2209_ = crate::leanh::lean_apply_2(v_h__3_2198_, v_a_2207_, v_b_2208_);
            return v___x_2209_;
        }
        3 => {
            let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2202_);
            crate::leanh::lean_dec(v_h__6_2201_);
            crate::leanh::lean_dec(v_h__5_2200_);
            crate::leanh::lean_dec(v_h__3_2198_);
            crate::leanh::lean_dec(v_h__2_2197_);
            crate::leanh::lean_dec(v_h__1_2196_);
            v_a_2210_ = crate::leanh::lean_ctor_get(v_x_2195_, 0);
            crate::leanh::lean_inc(v_a_2210_);
            v_b_2211_ = crate::leanh::lean_ctor_get(v_x_2195_, 1);
            crate::leanh::lean_inc(v_b_2211_);
            crate::leanh::lean_dec_ref_known(v_x_2195_, 2);
            v___x_2212_ = crate::leanh::lean_apply_2(v_h__4_2199_, v_a_2210_, v_b_2211_);
            return v___x_2212_;
        }
        4 => {
            let mut v_a_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_2201_);
            crate::leanh::lean_dec(v_h__5_2200_);
            crate::leanh::lean_dec(v_h__4_2199_);
            crate::leanh::lean_dec(v_h__3_2198_);
            crate::leanh::lean_dec(v_h__2_2197_);
            crate::leanh::lean_dec(v_h__1_2196_);
            v_a_2213_ = crate::leanh::lean_ctor_get(v_x_2195_, 0);
            crate::leanh::lean_inc(v_a_2213_);
            crate::leanh::lean_dec_ref_known(v_x_2195_, 1);
            v___x_2214_ = crate::leanh::lean_apply_1(v_h__7_2202_, v_a_2213_);
            return v___x_2214_;
        }
        5 => {
            let mut v_k_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2202_);
            crate::leanh::lean_dec(v_h__6_2201_);
            crate::leanh::lean_dec(v_h__4_2199_);
            crate::leanh::lean_dec(v_h__3_2198_);
            crate::leanh::lean_dec(v_h__2_2197_);
            crate::leanh::lean_dec(v_h__1_2196_);
            v_k_2215_ = crate::leanh::lean_ctor_get(v_x_2195_, 0);
            crate::leanh::lean_inc(v_k_2215_);
            v_a_2216_ = crate::leanh::lean_ctor_get(v_x_2195_, 1);
            crate::leanh::lean_inc(v_a_2216_);
            crate::leanh::lean_dec_ref_known(v_x_2195_, 2);
            v___x_2217_ = crate::leanh::lean_apply_2(v_h__5_2200_, v_k_2215_, v_a_2216_);
            return v___x_2217_;
        }
        _ => {
            let mut v_k_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_2202_);
            crate::leanh::lean_dec(v_h__5_2200_);
            crate::leanh::lean_dec(v_h__4_2199_);
            crate::leanh::lean_dec(v_h__3_2198_);
            crate::leanh::lean_dec(v_h__2_2197_);
            crate::leanh::lean_dec(v_h__1_2196_);
            v_k_2218_ = crate::leanh::lean_ctor_get(v_x_2195_, 0);
            crate::leanh::lean_inc(v_k_2218_);
            v_a_2219_ = crate::leanh::lean_ctor_get(v_x_2195_, 1);
            crate::leanh::lean_inc(v_a_2219_);
            crate::leanh::lean_dec_ref_known(v_x_2195_, 2);
            v___x_2220_ = crate::leanh::lean_apply_2(v_h__6_2201_, v_k_2218_, v_a_2219_);
            return v___x_2220_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_leadCoeff(
    mut v_p_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2221_) == 1 {
        let mut v_k_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_2222_ = crate::leanh::lean_ctor_get(v_p_2221_, 0);
        crate::leanh::lean_inc(v_k_2222_);
        return v_k_2222_;
    } else {
        let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2223_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        return v___x_2223_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(
    mut v_p_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2225_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_2224_);
    crate::leanh::lean_dec(v_p_2224_);
    return v_res_2225_;
}
pub unsafe fn l_Lean_Grind_Linarith_le__le__combine__cert(
    mut v_p_u2081_2226_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2227_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2228_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_u2082_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    v___x_2229_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_2226_);
    v_a_u2081_2230_ = lean_nat_abs(v___x_2229_);
    crate::leanh::lean_dec(v___x_2229_);
    v___x_2231_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_2227_);
    v_a_u2082_2232_ = lean_nat_abs(v___x_2231_);
    crate::leanh::lean_dec(v___x_2231_);
    v___x_2233_ = lean_nat_to_int(v_a_u2082_2232_);
    v___x_2234_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2226_, v___x_2233_);
    crate::leanh::lean_dec(v___x_2233_);
    v___x_2235_ = lean_nat_to_int(v_a_u2081_2230_);
    v___x_2236_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2227_, v___x_2235_);
    crate::leanh::lean_dec(v___x_2235_);
    v___x_2237_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2234_, v___x_2236_);
    v___x_2238_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2228_, v___x_2237_);
    crate::leanh::lean_dec(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_Grind_Linarith_le__le__combine__cert___boxed(
    mut v_p_u2081_2239_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2240_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2242_: u8 = 0;
    let mut v_r_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2242_ = l_Lean_Grind_Linarith_le__le__combine__cert(
        v_p_u2081_2239_,
        v_p_u2082_2240_,
        v_p_u2083_2241_,
    );
    crate::leanh::lean_dec(v_p_u2083_2241_);
    v_r_2243_ = crate::leanh::lean_box((v_res_2242_) as usize);
    return v_r_2243_;
}
pub unsafe fn l_Lean_Grind_Linarith_le__lt__combine__cert(
    mut v_p_u2081_2244_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2245_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2246_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    v___x_2247_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_2244_);
    v_a_u2081_2248_ = lean_nat_abs(v___x_2247_);
    crate::leanh::lean_dec(v___x_2247_);
    v___x_2249_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2250_ = lean_nat_to_int(v_a_u2081_2248_);
    v___x_2251_ = lean_int_dec_lt(v___x_2249_, v___x_2250_);
    if v___x_2251_ == 0 {
        crate::leanh::lean_dec(v___x_2250_);
        crate::leanh::lean_dec(v_p_u2082_2245_);
        crate::leanh::lean_dec(v_p_u2081_2244_);
        return v___x_2251_;
    } else {
        let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_u2082_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: u8 = 0;
        v___x_2252_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_2245_);
        v_a_u2082_2253_ = lean_nat_abs(v___x_2252_);
        crate::leanh::lean_dec(v___x_2252_);
        v___x_2254_ = lean_nat_to_int(v_a_u2082_2253_);
        v___x_2255_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2244_, v___x_2254_);
        crate::leanh::lean_dec(v___x_2254_);
        v___x_2256_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2245_, v___x_2250_);
        crate::leanh::lean_dec(v___x_2250_);
        v___x_2257_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2255_, v___x_2256_);
        v___x_2258_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2246_, v___x_2257_);
        crate::leanh::lean_dec(v___x_2257_);
        return v___x_2258_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(
    mut v_p_u2081_2259_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2260_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2262_: u8 = 0;
    let mut v_r_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Lean_Grind_Linarith_le__lt__combine__cert(
        v_p_u2081_2259_,
        v_p_u2082_2260_,
        v_p_u2083_2261_,
    );
    crate::leanh::lean_dec(v_p_u2083_2261_);
    v_r_2263_ = crate::leanh::lean_box((v_res_2262_) as usize);
    return v_r_2263_;
}
pub unsafe fn l_Lean_Grind_Linarith_lt__lt__combine__cert(
    mut v_p_u2081_2264_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2265_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2266_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_u2082_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: u8 = 0;
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: u8 = 0;
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2267_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_2264_);
                v_a_u2081_2268_ = lean_nat_abs(v___x_2267_);
                crate::leanh::lean_dec(v___x_2267_);
                v___x_2269_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_2265_);
                v_a_u2082_2270_ = lean_nat_abs(v___x_2269_);
                crate::leanh::lean_dec(v___x_2269_);
                v___x_2279_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                crate::leanh::lean_inc(v_a_u2082_2270_);
                v___x_2280_ = lean_nat_to_int(v_a_u2082_2270_);
                v___x_2281_ = lean_int_dec_lt(v___x_2279_, v___x_2280_);
                crate::leanh::lean_dec(v___x_2280_);
                if v___x_2281_ == 0 {
                    v___y_2272_ = v___x_2281_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_u2081_2268_);
                    v___x_2282_ = lean_nat_to_int(v_a_u2081_2268_);
                    v___x_2283_ = lean_int_dec_lt(v___x_2279_, v___x_2282_);
                    crate::leanh::lean_dec(v___x_2282_);
                    v___y_2272_ = v___x_2283_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2272_ == 0 {
                    crate::leanh::lean_dec(v_a_u2082_2270_);
                    crate::leanh::lean_dec(v_a_u2081_2268_);
                    crate::leanh::lean_dec(v_p_u2082_2265_);
                    crate::leanh::lean_dec(v_p_u2081_2264_);
                    return v___y_2272_;
                } else {
                    v___x_2273_ = lean_nat_to_int(v_a_u2082_2270_);
                    v___x_2274_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2264_, v___x_2273_);
                    crate::leanh::lean_dec(v___x_2273_);
                    v___x_2275_ = lean_nat_to_int(v_a_u2081_2268_);
                    v___x_2276_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2265_, v___x_2275_);
                    crate::leanh::lean_dec(v___x_2275_);
                    v___x_2277_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2274_, v___x_2276_);
                    v___x_2278_ =
                        l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2266_, v___x_2277_);
                    crate::leanh::lean_dec(v___x_2277_);
                    return v___x_2278_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(
    mut v_p_u2081_2284_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2285_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2287_: u8 = 0;
    let mut v_r_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2287_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(
        v_p_u2081_2284_,
        v_p_u2082_2285_,
        v_p_u2083_2286_,
    );
    crate::leanh::lean_dec(v_p_u2083_2286_);
    v_r_2288_ = crate::leanh::lean_box((v_res_2287_) as usize);
    return v_r_2288_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2290_ = lean_int_neg(v___x_2289_);
    return v___x_2290_;
}
pub unsafe fn l_Lean_Grind_Linarith_diseq__split__cert(
    mut v_p_u2081_2291_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2292_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    v___x_2293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2294_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2291_, v___x_2293_);
    v___x_2295_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_2292_, v___x_2294_);
    crate::leanh::lean_dec(v___x_2294_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_Grind_Linarith_diseq__split__cert___boxed(
    mut v_p_u2081_2296_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2298_: u8 = 0;
    let mut v_r_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_2296_, v_p_u2082_2297_);
    crate::leanh::lean_dec(v_p_u2082_2297_);
    v_r_2299_ = crate::leanh::lean_box((v_res_2298_) as usize);
    return v_r_2299_;
}
pub unsafe fn l_Lean_Grind_Linarith_norm__cert(
    mut v_lhs_2300_: *mut crate::leanh::LeanObject,
    mut v_rhs_2301_: *mut crate::leanh::LeanObject,
    mut v_p_2302_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    v___x_2303_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2303_, 0, v_lhs_2300_);
    crate::leanh::lean_ctor_set(v___x_2303_, 1, v_rhs_2301_);
    v___x_2304_ = l_Lean_Grind_Linarith_Expr_norm(v___x_2303_);
    v___x_2305_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2302_, v___x_2304_);
    crate::leanh::lean_dec(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn l_Lean_Grind_Linarith_norm__cert___boxed(
    mut v_lhs_2306_: *mut crate::leanh::LeanObject,
    mut v_rhs_2307_: *mut crate::leanh::LeanObject,
    mut v_p_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2309_: u8 = 0;
    let mut v_r_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Lean_Grind_Linarith_norm__cert(v_lhs_2306_, v_rhs_2307_, v_p_2308_);
    crate::leanh::lean_dec(v_p_2308_);
    v_r_2310_ = crate::leanh::lean_box((v_res_2309_) as usize);
    return v_r_2310_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__of__le__ge__cert(
    mut v_p_u2081_2311_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2312_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: u8 = 0;
    v___x_2313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2314_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2311_, v___x_2313_);
    v___x_2315_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_2312_, v___x_2314_);
    crate::leanh::lean_dec(v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(
    mut v_p_u2081_2316_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2318_: u8 = 0;
    let mut v_r_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2318_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_2316_, v_p_u2082_2317_);
    crate::leanh::lean_dec(v_p_u2082_2317_);
    v_r_2319_ = crate::leanh::lean_box((v_res_2318_) as usize);
    return v_r_2319_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = crate::leanh::lean_box(0);
    v___x_2321_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2323_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2322_);
    crate::leanh::lean_ctor_set(v___x_2323_, 1, v___x_2321_);
    crate::leanh::lean_ctor_set(v___x_2323_, 2, v___x_2320_);
    return v___x_2323_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__lt__one__cert(
    mut v_p_2324_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    v___x_2325_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0,
    );
    v___x_2326_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2324_, v___x_2325_);
    return v___x_2326_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(
    mut v_p_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2328_: u8 = 0;
    let mut v_r_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_2327_);
    crate::leanh::lean_dec(v_p_2327_);
    v_r_2329_ = crate::leanh::lean_box((v_res_2328_) as usize);
    return v_r_2329_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = crate::leanh::lean_box(0);
    v___x_2331_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2332_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2333_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    crate::leanh::lean_ctor_set(v___x_2333_, 1, v___x_2331_);
    crate::leanh::lean_ctor_set(v___x_2333_, 2, v___x_2330_);
    return v___x_2333_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__cert(
    mut v_p_2334_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    v___x_2335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0,
    );
    v___x_2336_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2334_, v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(
    mut v_p_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2338_: u8 = 0;
    let mut v_r_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_2337_);
    crate::leanh::lean_dec(v_p_2337_);
    v_r_2339_ = crate::leanh::lean_box((v_res_2338_) as usize);
    return v_r_2339_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(
    mut v_c_2340_: *mut crate::leanh::LeanObject,
    mut v_p_2341_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    v___x_2342_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2343_ = lean_nat_to_int(v_c_2340_);
    v___x_2344_ = lean_int_dec_lt(v___x_2342_, v___x_2343_);
    crate::leanh::lean_dec(v___x_2343_);
    if v___x_2344_ == 0 {
        return v___x_2344_;
    } else {
        let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: u8 = 0;
        v___x_2345_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once),
            _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0,
        );
        v___x_2346_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2341_, v___x_2345_);
        return v___x_2346_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(
    mut v_c_2347_: *mut crate::leanh::LeanObject,
    mut v_p_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: u8 = 0;
    let mut v_r_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_2347_, v_p_2348_);
    crate::leanh::lean_dec(v_p_2348_);
    v_r_2350_ = crate::leanh::lean_box((v_res_2349_) as usize);
    return v_r_2350_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__neg__cert(
    mut v_p_u2081_2351_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2352_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    v___x_2353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2354_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2351_, v___x_2353_);
    v___x_2355_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_2352_, v___x_2354_);
    crate::leanh::lean_dec(v___x_2354_);
    return v___x_2355_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__neg__cert___boxed(
    mut v_p_u2081_2356_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2358_: u8 = 0;
    let mut v_r_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_2356_, v_p_u2082_2357_);
    crate::leanh::lean_dec(v_p_u2082_2357_);
    v_r_2359_ = crate::leanh::lean_box((v_res_2358_) as usize);
    return v_r_2359_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__coeff__cert(
    mut v_p_u2081_2360_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2361_: *mut crate::leanh::LeanObject,
    mut v_k_2362_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: u8 = 0;
    v___x_2363_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2364_ = lean_nat_dec_eq(v_k_2362_, v___x_2363_);
    if v___x_2364_ == 0 {
        let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: u8 = 0;
        v___x_2365_ = lean_nat_to_int(v_k_2362_);
        v___x_2366_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2361_, v___x_2365_);
        crate::leanh::lean_dec(v___x_2365_);
        v___x_2367_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_2360_, v___x_2366_);
        crate::leanh::lean_dec(v___x_2366_);
        return v___x_2367_;
    } else {
        let mut v___x_2368_: u8 = 0;
        crate::leanh::lean_dec(v_k_2362_);
        crate::leanh::lean_dec(v_p_u2082_2361_);
        v___x_2368_ = 0;
        return v___x_2368_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__coeff__cert___boxed(
    mut v_p_u2081_2369_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2370_: *mut crate::leanh::LeanObject,
    mut v_k_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2372_: u8 = 0;
    let mut v_r_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2372_ =
        l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_2369_, v_p_u2082_2370_, v_k_2371_);
    crate::leanh::lean_dec(v_p_u2081_2369_);
    v_r_2373_ = crate::leanh::lean_box((v_res_2372_) as usize);
    return v_r_2373_;
}
pub unsafe fn l_Lean_Grind_Linarith_coeff__cert(
    mut v_p_u2081_2374_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2375_: *mut crate::leanh::LeanObject,
    mut v_k_2376_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    v___x_2377_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2378_ = lean_nat_dec_lt(v___x_2377_, v_k_2376_);
    if v___x_2378_ == 0 {
        crate::leanh::lean_dec(v_k_2376_);
        crate::leanh::lean_dec(v_p_u2082_2375_);
        return v___x_2378_;
    } else {
        let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2381_: u8 = 0;
        v___x_2379_ = lean_nat_to_int(v_k_2376_);
        v___x_2380_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2375_, v___x_2379_);
        crate::leanh::lean_dec(v___x_2379_);
        v___x_2381_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_2374_, v___x_2380_);
        crate::leanh::lean_dec(v___x_2380_);
        return v___x_2381_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_coeff__cert___boxed(
    mut v_p_u2081_2382_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2383_: *mut crate::leanh::LeanObject,
    mut v_k_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: u8 = 0;
    let mut v_r_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_2382_, v_p_u2082_2383_, v_k_2384_);
    crate::leanh::lean_dec(v_p_u2081_2382_);
    v_r_2386_ = crate::leanh::lean_box((v_res_2385_) as usize);
    return v_r_2386_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst__cert(
    mut v_k_u2081_2387_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_2388_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2389_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2390_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2391_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    v___x_2392_ = lean_nat_abs(v_k_u2081_2387_);
    v___x_2393_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2394_ = lean_nat_dec_eq(v___x_2392_, v___x_2393_);
    crate::leanh::lean_dec(v___x_2392_);
    if v___x_2394_ == 0 {
        let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: u8 = 0;
        v___x_2395_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2389_, v_k_u2082_2388_);
        v___x_2396_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2390_, v_k_u2081_2387_);
        v___x_2397_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2395_, v___x_2396_);
        v___x_2398_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2391_, v___x_2397_);
        crate::leanh::lean_dec(v___x_2397_);
        return v___x_2398_;
    } else {
        let mut v___x_2399_: u8 = 0;
        crate::leanh::lean_dec(v_p_u2082_2390_);
        crate::leanh::lean_dec(v_p_u2081_2389_);
        v___x_2399_ = 0;
        return v___x_2399_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(
    mut v_k_u2081_2400_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_2401_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2402_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2403_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2405_: u8 = 0;
    let mut v_r_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(
        v_k_u2081_2400_,
        v_k_u2082_2401_,
        v_p_u2081_2402_,
        v_p_u2082_2403_,
        v_p_u2083_2404_,
    );
    crate::leanh::lean_dec(v_p_u2083_2404_);
    crate::leanh::lean_dec(v_k_u2082_2401_);
    crate::leanh::lean_dec(v_k_u2081_2400_);
    v_r_2406_ = crate::leanh::lean_box((v_res_2405_) as usize);
    return v_r_2406_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst1__cert(
    mut v_k_2407_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2408_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2409_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2410_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    v___x_2411_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2408_, v_k_2407_);
    v___x_2412_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2411_, v_p_u2082_2409_);
    v___x_2413_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2410_, v___x_2412_);
    crate::leanh::lean_dec(v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(
    mut v_k_2414_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2415_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2416_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2418_: u8 = 0;
    let mut v_r_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(
        v_k_2414_,
        v_p_u2081_2415_,
        v_p_u2082_2416_,
        v_p_u2083_2417_,
    );
    crate::leanh::lean_dec(v_p_u2083_2417_);
    crate::leanh::lean_dec(v_k_2414_);
    v_r_2419_ = crate::leanh::lean_box((v_res_2418_) as usize);
    return v_r_2419_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__le__subst__cert(
    mut v_x_2420_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2421_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2422_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2423_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    v_a_2424_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_2421_, v_x_2420_);
    v___x_2425_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2426_ = lean_int_dec_le(v___x_2425_, v_a_2424_);
    if v___x_2426_ == 0 {
        crate::leanh::lean_dec(v_a_2424_);
        crate::leanh::lean_dec(v_p_u2082_2422_);
        crate::leanh::lean_dec(v_p_u2081_2421_);
        return v___x_2426_;
    } else {
        let mut v_b_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: u8 = 0;
        v_b_2427_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_2422_, v_x_2420_);
        v___x_2428_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2422_, v_a_2424_);
        crate::leanh::lean_dec(v_a_2424_);
        v___x_2429_ = lean_int_neg(v_b_2427_);
        crate::leanh::lean_dec(v_b_2427_);
        v___x_2430_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2421_, v___x_2429_);
        crate::leanh::lean_dec(v___x_2429_);
        v___x_2431_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2428_, v___x_2430_);
        v___x_2432_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2423_, v___x_2431_);
        crate::leanh::lean_dec(v___x_2431_);
        return v___x_2432_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(
    mut v_x_2433_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2434_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2435_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: u8 = 0;
    let mut v_r_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Lean_Grind_Linarith_eq__le__subst__cert(
        v_x_2433_,
        v_p_u2081_2434_,
        v_p_u2082_2435_,
        v_p_u2083_2436_,
    );
    crate::leanh::lean_dec(v_p_u2083_2436_);
    crate::leanh::lean_dec(v_x_2433_);
    v_r_2438_ = crate::leanh::lean_box((v_res_2437_) as usize);
    return v_r_2438_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__lt__subst__cert(
    mut v_x_2439_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2440_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2441_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2442_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    v_a_2443_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_2440_, v_x_2439_);
    v___x_2444_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2445_ = lean_int_dec_lt(v___x_2444_, v_a_2443_);
    if v___x_2445_ == 0 {
        crate::leanh::lean_dec(v_a_2443_);
        crate::leanh::lean_dec(v_p_u2082_2441_);
        crate::leanh::lean_dec(v_p_u2081_2440_);
        return v___x_2445_;
    } else {
        let mut v_b_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: u8 = 0;
        v_b_2446_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_2441_, v_x_2439_);
        v___x_2447_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2441_, v_a_2443_);
        crate::leanh::lean_dec(v_a_2443_);
        v___x_2448_ = lean_int_neg(v_b_2446_);
        crate::leanh::lean_dec(v_b_2446_);
        v___x_2449_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2440_, v___x_2448_);
        crate::leanh::lean_dec(v___x_2448_);
        v___x_2450_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2447_, v___x_2449_);
        v___x_2451_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2442_, v___x_2450_);
        crate::leanh::lean_dec(v___x_2450_);
        return v___x_2451_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(
    mut v_x_2452_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2453_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2454_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2456_: u8 = 0;
    let mut v_r_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(
        v_x_2452_,
        v_p_u2081_2453_,
        v_p_u2082_2454_,
        v_p_u2083_2455_,
    );
    crate::leanh::lean_dec(v_p_u2083_2455_);
    crate::leanh::lean_dec(v_x_2452_);
    v_r_2457_ = crate::leanh::lean_box((v_res_2456_) as usize);
    return v_r_2457_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__eq__subst__cert(
    mut v_x_2458_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2459_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2460_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2461_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u8 = 0;
    v_a_2462_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_2459_, v_x_2458_);
    v_b_2463_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_2460_, v_x_2458_);
    v___x_2464_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2460_, v_a_2462_);
    crate::leanh::lean_dec(v_a_2462_);
    v___x_2465_ = lean_int_neg(v_b_2463_);
    crate::leanh::lean_dec(v_b_2463_);
    v___x_2466_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2459_, v___x_2465_);
    crate::leanh::lean_dec(v___x_2465_);
    v___x_2467_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2464_, v___x_2466_);
    v___x_2468_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2461_, v___x_2467_);
    crate::leanh::lean_dec(v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(
    mut v_x_2469_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2470_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2471_: *mut crate::leanh::LeanObject,
    mut v_p_u2083_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: u8 = 0;
    let mut v_r_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(
        v_x_2469_,
        v_p_u2081_2470_,
        v_p_u2082_2471_,
        v_p_u2083_2472_,
    );
    crate::leanh::lean_dec(v_p_u2083_2472_);
    crate::leanh::lean_dec(v_x_2469_);
    v_r_2474_ = crate::leanh::lean_box((v_res_2473_) as usize);
    return v_r_2474_;
}
pub unsafe fn l_Lean_Grind_Linarith_imp__eq__cert(
    mut v_p_2475_: *mut crate::leanh::LeanObject,
    mut v_x_2476_: *mut crate::leanh::LeanObject,
    mut v_y_2477_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    v___x_2478_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2479_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2480_ = crate::leanh::lean_box(0);
    v___x_2481_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2481_, 0, v___x_2479_);
    crate::leanh::lean_ctor_set(v___x_2481_, 1, v_y_2477_);
    crate::leanh::lean_ctor_set(v___x_2481_, 2, v___x_2480_);
    v___x_2482_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2478_);
    crate::leanh::lean_ctor_set(v___x_2482_, 1, v_x_2476_);
    crate::leanh::lean_ctor_set(v___x_2482_, 2, v___x_2481_);
    v___x_2483_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2475_, v___x_2482_);
    crate::leanh::lean_dec_ref_known(v___x_2482_, 3);
    return v___x_2483_;
}
pub unsafe fn l_Lean_Grind_Linarith_imp__eq__cert___boxed(
    mut v_p_2484_: *mut crate::leanh::LeanObject,
    mut v_x_2485_: *mut crate::leanh::LeanObject,
    mut v_y_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2487_: u8 = 0;
    let mut v_r_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2487_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_2484_, v_x_2485_, v_y_2486_);
    crate::leanh::lean_dec(v_p_2484_);
    v_r_2488_ = crate::leanh::lean_box((v_res_2487_) as usize);
    return v_r_2488_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ordered_Linarith(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Field(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
    l_Lean_Grind_Linarith_instInhabitedExpr_default =
        _init_l_Lean_Grind_Linarith_instInhabitedExpr_default();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Linarith_instInhabitedExpr_default);
    l_Lean_Grind_Linarith_instInhabitedExpr = _init_l_Lean_Grind_Linarith_instInhabitedExpr();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Linarith_instInhabitedExpr);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ordered_Linarith(
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
pub unsafe fn initialize_Init_Grind_Ordered_Linarith(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Field(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ordered_Linarith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Ordered_Linarith(builtin);
}
