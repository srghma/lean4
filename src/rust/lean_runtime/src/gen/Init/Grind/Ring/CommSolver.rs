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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_apply_5, lean_apply_6, lean_box, lean_box_uint64, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedExpr_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedExpr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instBEqExpr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instHashableExpr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instHashableExpr_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instHashableExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableExpr___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashableExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 110, 117, 109, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 110, 97, 116, 67, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 105, 110, 116, 67, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__16_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__19_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__22_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__25_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 69, 120, 112, 114, 46, 112, 111, 119, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr_repr___closed__28_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprExpr_repr___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprExpr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instReprExpr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instReprExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instBEqPower___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqPower_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqPower___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPower___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqPower: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPower___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPower___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instReprPower_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instReprPower___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprPower: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPower___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instInhabitedPower_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instInhabitedPower: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instHashablePower___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instHashablePower_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instHashablePower___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePower___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashablePower: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePower___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instBEqMon___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqMon_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqMon___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqMon___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqMon: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqMon___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 77, 111, 110, 46, 117, 110, 105, 116, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 77, 111, 110, 46, 109, 117, 108, 116, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon_repr___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprMon_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprMon___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instReprMon_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instReprMon___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprMon: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprMon___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instInhabitedMon_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedMon: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instHashableMon___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instHashableMon_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instHashableMon___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableMon___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashableMon: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashableMon___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_hugeFuel: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instBEqPoly___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instBEqPoly_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instBEqPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPoly___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instBEqPoly: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instBEqPoly___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 80, 111, 108, 121, 46, 110, 117, 109, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103,
            46, 80, 111, 108, 121, 46, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly_repr___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_instReprPoly_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_instReprPoly___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instReprPoly_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instReprPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instReprPoly: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instReprPoly___closed__0_value) as *mut LeanObject;
static mut l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedPoly_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_CommRing_instInhabitedPoly: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_instHashablePoly___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_CommRing_instHashablePoly_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_CommRing_instHashablePoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePoly___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_CommRing_instHashablePoly: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_instHashablePoly___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Grind_CommRing_Poly_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Poly_pow___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Expr_toPoly___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorIdx(
    mut v_x_3770_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3770_) {
        0 => {
            let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
            v___x_3771_ = lean_unsigned_to_nat(0);
            return v___x_3771_;
        }
        1 => {
            let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
            v___x_3772_ = lean_unsigned_to_nat(1);
            return v___x_3772_;
        }
        2 => {
            let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
            v___x_3773_ = lean_unsigned_to_nat(2);
            return v___x_3773_;
        }
        3 => {
            let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
            v___x_3774_ = lean_unsigned_to_nat(3);
            return v___x_3774_;
        }
        4 => {
            let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
            v___x_3775_ = lean_unsigned_to_nat(4);
            return v___x_3775_;
        }
        5 => {
            let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
            v___x_3776_ = lean_unsigned_to_nat(5);
            return v___x_3776_;
        }
        6 => {
            let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
            v___x_3777_ = lean_unsigned_to_nat(6);
            return v___x_3777_;
        }
        7 => {
            let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
            v___x_3778_ = lean_unsigned_to_nat(7);
            return v___x_3778_;
        }
        _ => {
            let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
            v___x_3779_ = lean_unsigned_to_nat(8);
            return v___x_3779_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorIdx___boxed(
    mut v_x_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Lean_Grind_CommRing_Expr_ctorIdx(v_x_3780_);
    lean_dec_ref(v_x_3780_);
    return v_res_3781_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorElim___redArg(
    mut v_t_3782_: *mut LeanObject,
    mut v_k_3783_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_3782_) {
        4 => {
            let mut v_a_3784_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
            v_a_3784_ = lean_ctor_get(v_t_3782_, 0);
            lean_inc_ref(v_a_3784_);
            lean_dec_ref_known(v_t_3782_, 1);
            v___x_3785_ = lean_apply_1(v_k_3783_, v_a_3784_);
            return v___x_3785_;
        }
        5 => {
            let mut v_a_3786_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_3787_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
            v_a_3786_ = lean_ctor_get(v_t_3782_, 0);
            lean_inc_ref(v_a_3786_);
            v_b_3787_ = lean_ctor_get(v_t_3782_, 1);
            lean_inc_ref(v_b_3787_);
            lean_dec_ref_known(v_t_3782_, 2);
            v___x_3788_ = lean_apply_2(v_k_3783_, v_a_3786_, v_b_3787_);
            return v___x_3788_;
        }
        6 => {
            let mut v_a_3789_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_3790_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
            v_a_3789_ = lean_ctor_get(v_t_3782_, 0);
            lean_inc_ref(v_a_3789_);
            v_b_3790_ = lean_ctor_get(v_t_3782_, 1);
            lean_inc_ref(v_b_3790_);
            lean_dec_ref_known(v_t_3782_, 2);
            v___x_3791_ = lean_apply_2(v_k_3783_, v_a_3789_, v_b_3790_);
            return v___x_3791_;
        }
        7 => {
            let mut v_a_3792_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_3793_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
            v_a_3792_ = lean_ctor_get(v_t_3782_, 0);
            lean_inc_ref(v_a_3792_);
            v_b_3793_ = lean_ctor_get(v_t_3782_, 1);
            lean_inc_ref(v_b_3793_);
            lean_dec_ref_known(v_t_3782_, 2);
            v___x_3794_ = lean_apply_2(v_k_3783_, v_a_3792_, v_b_3793_);
            return v___x_3794_;
        }
        8 => {
            let mut v_a_3795_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_3796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
            v_a_3795_ = lean_ctor_get(v_t_3782_, 0);
            lean_inc_ref(v_a_3795_);
            v_k_3796_ = lean_ctor_get(v_t_3782_, 1);
            lean_inc(v_k_3796_);
            lean_dec_ref_known(v_t_3782_, 2);
            v___x_3797_ = lean_apply_2(v_k_3783_, v_a_3795_, v_k_3796_);
            return v___x_3797_;
        }
        _ => {
            let mut v_k_3798_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
            v_k_3798_ = lean_ctor_get(v_t_3782_, 0);
            lean_inc(v_k_3798_);
            lean_dec_ref(v_t_3782_);
            v___x_3799_ = lean_apply_1(v_k_3783_, v_k_3798_);
            return v___x_3799_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorElim(
    mut v_motive_3800_: *mut LeanObject,
    mut v_ctorIdx_3801_: *mut LeanObject,
    mut v_t_3802_: *mut LeanObject,
    mut v_h_3803_: *mut LeanObject,
    mut v_k_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    v___x_3805_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3802_, v_k_3804_);
    return v___x_3805_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_ctorElim___boxed(
    mut v_motive_3806_: *mut LeanObject,
    mut v_ctorIdx_3807_: *mut LeanObject,
    mut v_t_3808_: *mut LeanObject,
    mut v_h_3809_: *mut LeanObject,
    mut v_k_3810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3811_: *mut LeanObject = core::ptr::null_mut();
    v_res_3811_ = l_Lean_Grind_CommRing_Expr_ctorElim(
        v_motive_3806_,
        v_ctorIdx_3807_,
        v_t_3808_,
        v_h_3809_,
        v_k_3810_,
    );
    lean_dec(v_ctorIdx_3807_);
    return v_res_3811_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_num_elim___redArg(
    mut v_t_3812_: *mut LeanObject,
    mut v_num_3813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3812_, v_num_3813_);
    return v___x_3814_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_num_elim(
    mut v_motive_3815_: *mut LeanObject,
    mut v_t_3816_: *mut LeanObject,
    mut v_h_3817_: *mut LeanObject,
    mut v_num_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v___x_3819_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3816_, v_num_3818_);
    return v___x_3819_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(
    mut v_t_3820_: *mut LeanObject,
    mut v_natCast_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    v___x_3822_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3820_, v_natCast_3821_);
    return v___x_3822_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_natCast_elim(
    mut v_motive_3823_: *mut LeanObject,
    mut v_t_3824_: *mut LeanObject,
    mut v_h_3825_: *mut LeanObject,
    mut v_natCast_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3824_, v_natCast_3826_);
    return v___x_3827_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(
    mut v_t_3828_: *mut LeanObject,
    mut v_intCast_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3828_, v_intCast_3829_);
    return v___x_3830_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_intCast_elim(
    mut v_motive_3831_: *mut LeanObject,
    mut v_t_3832_: *mut LeanObject,
    mut v_h_3833_: *mut LeanObject,
    mut v_intCast_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    v___x_3835_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3832_, v_intCast_3834_);
    return v___x_3835_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_var_elim___redArg(
    mut v_t_3836_: *mut LeanObject,
    mut v_var_3837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    v___x_3838_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3836_, v_var_3837_);
    return v___x_3838_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_var_elim(
    mut v_motive_3839_: *mut LeanObject,
    mut v_t_3840_: *mut LeanObject,
    mut v_h_3841_: *mut LeanObject,
    mut v_var_3842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    v___x_3843_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3840_, v_var_3842_);
    return v___x_3843_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_neg_elim___redArg(
    mut v_t_3844_: *mut LeanObject,
    mut v_neg_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    v___x_3846_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3844_, v_neg_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_neg_elim(
    mut v_motive_3847_: *mut LeanObject,
    mut v_t_3848_: *mut LeanObject,
    mut v_h_3849_: *mut LeanObject,
    mut v_neg_3850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    v___x_3851_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3848_, v_neg_3850_);
    return v___x_3851_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_add_elim___redArg(
    mut v_t_3852_: *mut LeanObject,
    mut v_add_3853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3852_, v_add_3853_);
    return v___x_3854_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_add_elim(
    mut v_motive_3855_: *mut LeanObject,
    mut v_t_3856_: *mut LeanObject,
    mut v_h_3857_: *mut LeanObject,
    mut v_add_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3856_, v_add_3858_);
    return v___x_3859_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_sub_elim___redArg(
    mut v_t_3860_: *mut LeanObject,
    mut v_sub_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    v___x_3862_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3860_, v_sub_3861_);
    return v___x_3862_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_sub_elim(
    mut v_motive_3863_: *mut LeanObject,
    mut v_t_3864_: *mut LeanObject,
    mut v_h_3865_: *mut LeanObject,
    mut v_sub_3866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3864_, v_sub_3866_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_mul_elim___redArg(
    mut v_t_3868_: *mut LeanObject,
    mut v_mul_3869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3868_, v_mul_3869_);
    return v___x_3870_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_mul_elim(
    mut v_motive_3871_: *mut LeanObject,
    mut v_t_3872_: *mut LeanObject,
    mut v_h_3873_: *mut LeanObject,
    mut v_mul_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    v___x_3875_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3872_, v_mul_3874_);
    return v___x_3875_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_pow_elim___redArg(
    mut v_t_3876_: *mut LeanObject,
    mut v_pow_3877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    v___x_3878_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3876_, v_pow_3877_);
    return v___x_3878_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_pow_elim(
    mut v_motive_3879_: *mut LeanObject,
    mut v_t_3880_: *mut LeanObject,
    mut v_h_3881_: *mut LeanObject,
    mut v_pow_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v___x_3883_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_3880_, v_pow_3882_);
    return v___x_3883_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0() -> *mut LeanObject
{
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    v___x_3884_ = lean_unsigned_to_nat(0);
    v___x_3885_ = lean_nat_to_int(v___x_3884_);
    return v___x_3885_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1() -> *mut LeanObject
{
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    v___x_3886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_3887_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3887_, 0, v___x_3886_);
    return v___x_3887_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr_default() -> *mut LeanObject {
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    v___x_3888_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1,
    );
    return v___x_3888_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedExpr() -> *mut LeanObject {
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    v___x_3889_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
    return v___x_3889_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqExpr_beq(
    mut v_x_3890_: *mut LeanObject,
    mut v_x_3891_: *mut LeanObject,
) -> u8 {
    let mut v_a_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: u8 = 0;
    let mut v_k_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: u8 = 0;
    let mut v_k_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: u8 = 0;
    let mut v_k_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: u8 = 0;
    let mut v_i_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: u8 = 0;
    let mut v_a_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: u8 = 0;
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: u8 = 0;
    let mut v_a_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v_a_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v_a_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3890_) {
                0 => {
                    if lean_obj_tag(v_x_3891_) == 0 {
                        v_k_3899_ = lean_ctor_get(v_x_3890_, 0);
                        v_k_3900_ = lean_ctor_get(v_x_3891_, 0);
                        v___x_3901_ = lean_int_dec_eq(v_k_3899_, v_k_3900_);
                        return v___x_3901_;
                    } else {
                        v___x_3902_ = 0;
                        return v___x_3902_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_x_3891_) == 1 {
                        v_k_3903_ = lean_ctor_get(v_x_3890_, 0);
                        v_k_3904_ = lean_ctor_get(v_x_3891_, 0);
                        v___x_3905_ = lean_nat_dec_eq(v_k_3903_, v_k_3904_);
                        return v___x_3905_;
                    } else {
                        v___x_3906_ = 0;
                        return v___x_3906_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_x_3891_) == 2 {
                        v_k_3907_ = lean_ctor_get(v_x_3890_, 0);
                        v_k_3908_ = lean_ctor_get(v_x_3891_, 0);
                        v___x_3909_ = lean_int_dec_eq(v_k_3907_, v_k_3908_);
                        return v___x_3909_;
                    } else {
                        v___x_3910_ = 0;
                        return v___x_3910_;
                    }
                }
                3 => {
                    if lean_obj_tag(v_x_3891_) == 3 {
                        v_i_3911_ = lean_ctor_get(v_x_3890_, 0);
                        v_i_3912_ = lean_ctor_get(v_x_3891_, 0);
                        v___x_3913_ = lean_nat_dec_eq(v_i_3911_, v_i_3912_);
                        return v___x_3913_;
                    } else {
                        v___x_3914_ = 0;
                        return v___x_3914_;
                    }
                }
                4 => {
                    if lean_obj_tag(v_x_3891_) == 4 {
                        v_a_3915_ = lean_ctor_get(v_x_3890_, 0);
                        v_a_3916_ = lean_ctor_get(v_x_3891_, 0);
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
                    if lean_obj_tag(v_x_3891_) == 5 {
                        v_a_3919_ = lean_ctor_get(v_x_3890_, 0);
                        v_b_3920_ = lean_ctor_get(v_x_3890_, 1);
                        v_a_3921_ = lean_ctor_get(v_x_3891_, 0);
                        v_b_3922_ = lean_ctor_get(v_x_3891_, 1);
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
                    if lean_obj_tag(v_x_3891_) == 6 {
                        v_a_3924_ = lean_ctor_get(v_x_3890_, 0);
                        v_b_3925_ = lean_ctor_get(v_x_3890_, 1);
                        v_a_3926_ = lean_ctor_get(v_x_3891_, 0);
                        v_b_3927_ = lean_ctor_get(v_x_3891_, 1);
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
                    if lean_obj_tag(v_x_3891_) == 7 {
                        v_a_3929_ = lean_ctor_get(v_x_3890_, 0);
                        v_b_3930_ = lean_ctor_get(v_x_3890_, 1);
                        v_a_3931_ = lean_ctor_get(v_x_3891_, 0);
                        v_b_3932_ = lean_ctor_get(v_x_3891_, 1);
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
                    if lean_obj_tag(v_x_3891_) == 8 {
                        v_a_3934_ = lean_ctor_get(v_x_3890_, 0);
                        v_k_3935_ = lean_ctor_get(v_x_3890_, 1);
                        v_a_3936_ = lean_ctor_get(v_x_3891_, 0);
                        v_k_3937_ = lean_ctor_get(v_x_3891_, 1);
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
    mut v_x_3941_: *mut LeanObject,
    mut v_x_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3943_: u8 = 0;
    let mut v_r_3944_: *mut LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_x_3941_, v_x_3942_);
    lean_dec_ref(v_x_3942_);
    lean_dec_ref(v_x_3941_);
    v_r_3944_ = lean_box((v_res_3943_) as usize);
    return v_r_3944_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableExpr_hash(mut v_x_3947_: *mut LeanObject) -> u64 {
    match lean_obj_tag(v_x_3947_) {
        0 => {
            let mut v_k_3948_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3949_: u64 = 0;
            let mut v_intZero_3950_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isNeg_3951_: u8 = 0;
            v_k_3948_ = lean_ctor_get(v_x_3947_, 0);
            v___x_3949_ = 0u64;
            v_intZero_3950_ = lean_obj_once(
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
                let mut v_a_3952_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3955_: u64 = 0;
                let mut v___x_3956_: u64 = 0;
                v_a_3952_ = lean_nat_abs(v_k_3948_);
                v___x_3953_ = lean_unsigned_to_nat(2);
                v___x_3954_ = lean_nat_mul(v___x_3953_, v_a_3952_);
                lean_dec(v_a_3952_);
                v___x_3955_ = lean_uint64_of_nat(v___x_3954_);
                lean_dec(v___x_3954_);
                v___x_3956_ = lean_uint64_mix_hash(v___x_3949_, v___x_3955_);
                return v___x_3956_;
            } else {
                let mut v_abs_3957_: *mut LeanObject = core::ptr::null_mut();
                let mut v_one_3958_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_3959_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3963_: u64 = 0;
                let mut v___x_3964_: u64 = 0;
                v_abs_3957_ = lean_nat_abs(v_k_3948_);
                v_one_3958_ = lean_unsigned_to_nat(1);
                v_a_3959_ = lean_nat_sub(v_abs_3957_, v_one_3958_);
                lean_dec(v_abs_3957_);
                v___x_3960_ = lean_unsigned_to_nat(2);
                v___x_3961_ = lean_nat_mul(v___x_3960_, v_a_3959_);
                lean_dec(v_a_3959_);
                v___x_3962_ = lean_nat_add(v___x_3961_, v_one_3958_);
                lean_dec(v___x_3961_);
                v___x_3963_ = lean_uint64_of_nat(v___x_3962_);
                lean_dec(v___x_3962_);
                v___x_3964_ = lean_uint64_mix_hash(v___x_3949_, v___x_3963_);
                return v___x_3964_;
            }
        }
        1 => {
            let mut v_k_3965_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3966_: u64 = 0;
            let mut v___x_3967_: u64 = 0;
            let mut v___x_3968_: u64 = 0;
            v_k_3965_ = lean_ctor_get(v_x_3947_, 0);
            v___x_3966_ = 1u64;
            v___x_3967_ = lean_uint64_of_nat(v_k_3965_);
            v___x_3968_ = lean_uint64_mix_hash(v___x_3966_, v___x_3967_);
            return v___x_3968_;
        }
        2 => {
            let mut v_k_3969_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3970_: u64 = 0;
            let mut v_intZero_3971_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isNeg_3972_: u8 = 0;
            v_k_3969_ = lean_ctor_get(v_x_3947_, 0);
            v___x_3970_ = 2u64;
            v_intZero_3971_ = lean_obj_once(
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
                let mut v_a_3973_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3976_: u64 = 0;
                let mut v___x_3977_: u64 = 0;
                v_a_3973_ = lean_nat_abs(v_k_3969_);
                v___x_3974_ = lean_unsigned_to_nat(2);
                v___x_3975_ = lean_nat_mul(v___x_3974_, v_a_3973_);
                lean_dec(v_a_3973_);
                v___x_3976_ = lean_uint64_of_nat(v___x_3975_);
                lean_dec(v___x_3975_);
                v___x_3977_ = lean_uint64_mix_hash(v___x_3970_, v___x_3976_);
                return v___x_3977_;
            } else {
                let mut v_abs_3978_: *mut LeanObject = core::ptr::null_mut();
                let mut v_one_3979_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_3980_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3984_: u64 = 0;
                let mut v___x_3985_: u64 = 0;
                v_abs_3978_ = lean_nat_abs(v_k_3969_);
                v_one_3979_ = lean_unsigned_to_nat(1);
                v_a_3980_ = lean_nat_sub(v_abs_3978_, v_one_3979_);
                lean_dec(v_abs_3978_);
                v___x_3981_ = lean_unsigned_to_nat(2);
                v___x_3982_ = lean_nat_mul(v___x_3981_, v_a_3980_);
                lean_dec(v_a_3980_);
                v___x_3983_ = lean_nat_add(v___x_3982_, v_one_3979_);
                lean_dec(v___x_3982_);
                v___x_3984_ = lean_uint64_of_nat(v___x_3983_);
                lean_dec(v___x_3983_);
                v___x_3985_ = lean_uint64_mix_hash(v___x_3970_, v___x_3984_);
                return v___x_3985_;
            }
        }
        3 => {
            let mut v_i_3986_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3987_: u64 = 0;
            let mut v___x_3988_: u64 = 0;
            let mut v___x_3989_: u64 = 0;
            v_i_3986_ = lean_ctor_get(v_x_3947_, 0);
            v___x_3987_ = 3u64;
            v___x_3988_ = lean_uint64_of_nat(v_i_3986_);
            v___x_3989_ = lean_uint64_mix_hash(v___x_3987_, v___x_3988_);
            return v___x_3989_;
        }
        4 => {
            let mut v_a_3990_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3991_: u64 = 0;
            let mut v___x_3992_: u64 = 0;
            let mut v___x_3993_: u64 = 0;
            v_a_3990_ = lean_ctor_get(v_x_3947_, 0);
            v___x_3991_ = 4u64;
            v___x_3992_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_3990_);
            v___x_3993_ = lean_uint64_mix_hash(v___x_3991_, v___x_3992_);
            return v___x_3993_;
        }
        5 => {
            let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_3995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3996_: u64 = 0;
            let mut v___x_3997_: u64 = 0;
            let mut v___x_3998_: u64 = 0;
            let mut v___x_3999_: u64 = 0;
            let mut v___x_4000_: u64 = 0;
            v_a_3994_ = lean_ctor_get(v_x_3947_, 0);
            v_b_3995_ = lean_ctor_get(v_x_3947_, 1);
            v___x_3996_ = 5u64;
            v___x_3997_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_3994_);
            v___x_3998_ = lean_uint64_mix_hash(v___x_3996_, v___x_3997_);
            v___x_3999_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_3995_);
            v___x_4000_ = lean_uint64_mix_hash(v___x_3998_, v___x_3999_);
            return v___x_4000_;
        }
        6 => {
            let mut v_a_4001_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_4002_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4003_: u64 = 0;
            let mut v___x_4004_: u64 = 0;
            let mut v___x_4005_: u64 = 0;
            let mut v___x_4006_: u64 = 0;
            let mut v___x_4007_: u64 = 0;
            v_a_4001_ = lean_ctor_get(v_x_3947_, 0);
            v_b_4002_ = lean_ctor_get(v_x_3947_, 1);
            v___x_4003_ = 6u64;
            v___x_4004_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_4001_);
            v___x_4005_ = lean_uint64_mix_hash(v___x_4003_, v___x_4004_);
            v___x_4006_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_4002_);
            v___x_4007_ = lean_uint64_mix_hash(v___x_4005_, v___x_4006_);
            return v___x_4007_;
        }
        7 => {
            let mut v_a_4008_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_4009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4010_: u64 = 0;
            let mut v___x_4011_: u64 = 0;
            let mut v___x_4012_: u64 = 0;
            let mut v___x_4013_: u64 = 0;
            let mut v___x_4014_: u64 = 0;
            v_a_4008_ = lean_ctor_get(v_x_3947_, 0);
            v_b_4009_ = lean_ctor_get(v_x_3947_, 1);
            v___x_4010_ = 7u64;
            v___x_4011_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_4008_);
            v___x_4012_ = lean_uint64_mix_hash(v___x_4010_, v___x_4011_);
            v___x_4013_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_4009_);
            v___x_4014_ = lean_uint64_mix_hash(v___x_4012_, v___x_4013_);
            return v___x_4014_;
        }
        _ => {
            let mut v_a_4015_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4016_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4017_: u64 = 0;
            let mut v___x_4018_: u64 = 0;
            let mut v___x_4019_: u64 = 0;
            let mut v___x_4020_: u64 = 0;
            let mut v___x_4021_: u64 = 0;
            v_a_4015_ = lean_ctor_get(v_x_3947_, 0);
            v_k_4016_ = lean_ctor_get(v_x_3947_, 1);
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
    mut v_x_4022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4023_: u64 = 0;
    let mut v_r_4024_: *mut LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_x_4022_);
    lean_dec_ref(v_x_4022_);
    v_r_4024_ = lean_box_uint64(v_res_4023_);
    return v_r_4024_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3() -> *mut LeanObject {
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    v___x_4033_ = lean_unsigned_to_nat(2);
    v___x_4034_ = lean_nat_to_int(v___x_4033_);
    return v___x_4034_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4() -> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    v___x_4035_ = lean_unsigned_to_nat(1);
    v___x_4036_ = lean_nat_to_int(v___x_4035_);
    return v___x_4036_;
}
pub unsafe fn l_Lean_Grind_CommRing_instReprExpr_repr(
    mut v_x_4085_: *mut LeanObject,
    mut v_prec_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_k_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___y_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v_k_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___y_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut v_i_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___y_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_a_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_a_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v_a_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: u8 = 0;
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4085_) {
                0 => {
                    v_k_4105_ = lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4128_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4107_ = v_x_4085_;
                        v_isShared_4108_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_k_4105_);
                        lean_dec(v_x_4085_);
                        v___x_4107_ = lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_k_4129_ = lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4149_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4149_ == 0 {
                        v___x_4131_ = v_x_4085_;
                        v_isShared_4132_ = v_isSharedCheck_4149_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_k_4129_);
                        lean_dec(v_x_4085_);
                        v___x_4131_ = lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4149_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_k_4150_ = lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4173_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4173_ == 0 {
                        v___x_4152_ = v_x_4085_;
                        v_isShared_4153_ = v_isSharedCheck_4173_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_k_4150_);
                        lean_dec(v_x_4085_);
                        v___x_4152_ = lean_box(0);
                        v_isShared_4153_ = v_isSharedCheck_4173_;
                        state = 10;
                        continue;
                    }
                }
                3 => {
                    v_i_4174_ = lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4194_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4194_ == 0 {
                        v___x_4176_ = v_x_4085_;
                        v_isShared_4177_ = v_isSharedCheck_4194_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_i_4174_);
                        lean_dec(v_x_4085_);
                        v___x_4176_ = lean_box(0);
                        v_isShared_4177_ = v_isSharedCheck_4194_;
                        state = 14;
                        continue;
                    }
                }
                4 => {
                    v_a_4195_ = lean_ctor_get(v_x_4085_, 0);
                    lean_inc_ref(v_a_4195_);
                    lean_dec_ref_known(v_x_4085_, 1);
                    v___x_4196_ = lean_unsigned_to_nat(1024);
                    v___x_4206_ = lean_nat_dec_le(v___x_4196_, v_prec_4086_);
                    if v___x_4206_ == 0 {
                        v___x_4207_ = lean_obj_once(
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
                        v___x_4208_ = lean_obj_once(
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
                    v_a_4209_ = lean_ctor_get(v_x_4085_, 0);
                    v_b_4210_ = lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4233_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4212_ = v_x_4085_;
                        v_isShared_4213_ = v_isSharedCheck_4233_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_b_4210_);
                        lean_inc(v_a_4209_);
                        lean_dec(v_x_4085_);
                        v___x_4212_ = lean_box(0);
                        v_isShared_4213_ = v_isSharedCheck_4233_;
                        state = 18;
                        continue;
                    }
                }
                6 => {
                    v_a_4234_ = lean_ctor_get(v_x_4085_, 0);
                    v_b_4235_ = lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4258_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4258_ == 0 {
                        v___x_4237_ = v_x_4085_;
                        v_isShared_4238_ = v_isSharedCheck_4258_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_b_4235_);
                        lean_inc(v_a_4234_);
                        lean_dec(v_x_4085_);
                        v___x_4237_ = lean_box(0);
                        v_isShared_4238_ = v_isSharedCheck_4258_;
                        state = 21;
                        continue;
                    }
                }
                7 => {
                    v_a_4259_ = lean_ctor_get(v_x_4085_, 0);
                    v_b_4260_ = lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4283_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4283_ == 0 {
                        v___x_4262_ = v_x_4085_;
                        v_isShared_4263_ = v_isSharedCheck_4283_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_b_4260_);
                        lean_inc(v_a_4259_);
                        lean_dec(v_x_4085_);
                        v___x_4262_ = lean_box(0);
                        v_isShared_4263_ = v_isSharedCheck_4283_;
                        state = 24;
                        continue;
                    }
                }
                _ => {
                    v_a_4284_ = lean_ctor_get(v_x_4085_, 0);
                    v_k_4285_ = lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4309_ = (!lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4287_ = v_x_4085_;
                        v_isShared_4288_ = v_isSharedCheck_4309_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_k_4285_);
                        lean_inc(v_a_4284_);
                        lean_dec(v_x_4085_);
                        v___x_4287_ = lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4309_;
                        state = 27;
                        continue;
                    }
                }
            },
            1 => {
                lean_inc(v___y_4089_);
                v___x_4091_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4091_, 0, v___y_4089_);
                lean_ctor_set(v___x_4091_, 1, v___y_4090_);
                lean_inc(v___y_4088_);
                v___x_4092_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4092_, 0, v___y_4088_);
                lean_ctor_set(v___x_4092_, 1, v___x_4091_);
                v___x_4093_ = 0;
                v___x_4094_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4094_, 0, v___x_4092_);
                lean_ctor_set_uint8(
                    v___x_4094_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4093_,
                );
                v___x_4095_ = l_Repr_addAppParen(v___x_4094_, v_prec_4086_);
                return v___x_4095_;
            }
            2 => {
                lean_inc(v___y_4098_);
                v___x_4100_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4100_, 0, v___y_4098_);
                lean_ctor_set(v___x_4100_, 1, v___y_4099_);
                lean_inc(v___y_4097_);
                v___x_4101_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4101_, 0, v___y_4097_);
                lean_ctor_set(v___x_4101_, 1, v___x_4100_);
                v___x_4102_ = 0;
                v___x_4103_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4103_, 0, v___x_4101_);
                lean_ctor_set_uint8(
                    v___x_4103_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4102_,
                );
                v___x_4104_ = l_Repr_addAppParen(v___x_4103_, v_prec_4086_);
                return v___x_4104_;
            }
            3 => {
                v___x_4124_ = lean_unsigned_to_nat(1024);
                v___x_4125_ = lean_nat_dec_le(v___x_4124_, v_prec_4086_);
                if v___x_4125_ == 0 {
                    v___x_4126_ = lean_obj_once(
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
                    v___x_4127_ = lean_obj_once(
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
                v___x_4112_ = lean_obj_once(
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
                    lean_dec(v_k_4105_);
                    if v_isShared_4108_ == 0 {
                        lean_ctor_set_tag(v___x_4107_, 3);
                        lean_ctor_set(v___x_4107_, 0, v___x_4114_);
                        v___x_4116_ = v___x_4107_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4117_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
                        v___x_4116_ = v_reuseFailAlloc_4117_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_4118_ = lean_unsigned_to_nat(1024);
                    v___x_4119_ = l_Int_repr(v_k_4105_);
                    lean_dec(v_k_4105_);
                    if v_isShared_4108_ == 0 {
                        lean_ctor_set_tag(v___x_4107_, 3);
                        lean_ctor_set(v___x_4107_, 0, v___x_4119_);
                        v___x_4121_ = v___x_4107_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4123_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4119_);
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
                v___x_4145_ = lean_unsigned_to_nat(1024);
                v___x_4146_ = lean_nat_dec_le(v___x_4145_, v_prec_4086_);
                if v___x_4146_ == 0 {
                    v___x_4147_ = lean_obj_once(
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
                    v___x_4148_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_4131_, 3);
                    lean_ctor_set(v___x_4131_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4131_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4144_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4144_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4139_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4139_, 0, v___x_4135_);
                lean_ctor_set(v___x_4139_, 1, v___x_4138_);
                lean_inc(v___y_4134_);
                v___x_4140_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4140_, 0, v___y_4134_);
                lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = 0;
                v___x_4142_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4142_, 0, v___x_4140_);
                lean_ctor_set_uint8(
                    v___x_4142_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4141_,
                );
                v___x_4143_ = l_Repr_addAppParen(v___x_4142_, v_prec_4086_);
                return v___x_4143_;
            }
            10 => {
                v___x_4169_ = lean_unsigned_to_nat(1024);
                v___x_4170_ = lean_nat_dec_le(v___x_4169_, v_prec_4086_);
                if v___x_4170_ == 0 {
                    v___x_4171_ = lean_obj_once(
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
                    v___x_4172_ = lean_obj_once(
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
                v___x_4157_ = lean_obj_once(
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
                    lean_dec(v_k_4150_);
                    if v_isShared_4153_ == 0 {
                        lean_ctor_set_tag(v___x_4152_, 3);
                        lean_ctor_set(v___x_4152_, 0, v___x_4159_);
                        v___x_4161_ = v___x_4152_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4162_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
                        v___x_4161_ = v_reuseFailAlloc_4162_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_4163_ = lean_unsigned_to_nat(1024);
                    v___x_4164_ = l_Int_repr(v_k_4150_);
                    lean_dec(v_k_4150_);
                    if v_isShared_4153_ == 0 {
                        lean_ctor_set_tag(v___x_4152_, 3);
                        lean_ctor_set(v___x_4152_, 0, v___x_4164_);
                        v___x_4166_ = v___x_4152_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4168_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
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
                v___x_4190_ = lean_unsigned_to_nat(1024);
                v___x_4191_ = lean_nat_dec_le(v___x_4190_, v_prec_4086_);
                if v___x_4191_ == 0 {
                    v___x_4192_ = lean_obj_once(
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
                    v___x_4193_ = lean_obj_once(
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
                    lean_ctor_set(v___x_4176_, 0, v___x_4181_);
                    v___x_4183_ = v___x_4176_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4181_);
                    v___x_4183_ = v_reuseFailAlloc_4189_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4184_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4184_, 0, v___x_4180_);
                lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                lean_inc(v___y_4179_);
                v___x_4185_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4185_, 0, v___y_4179_);
                lean_ctor_set(v___x_4185_, 1, v___x_4184_);
                v___x_4186_ = 0;
                v___x_4187_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4187_, 0, v___x_4185_);
                lean_ctor_set_uint8(
                    v___x_4187_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4186_,
                );
                v___x_4188_ = l_Repr_addAppParen(v___x_4187_, v_prec_4086_);
                return v___x_4188_;
            }
            17 => {
                v___x_4199_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__16;
                v___x_4200_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4195_, v___x_4196_);
                v___x_4201_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4201_, 0, v___x_4199_);
                lean_ctor_set(v___x_4201_, 1, v___x_4200_);
                lean_inc(v___y_4198_);
                v___x_4202_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4202_, 0, v___y_4198_);
                lean_ctor_set(v___x_4202_, 1, v___x_4201_);
                v___x_4203_ = 0;
                v___x_4204_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4204_, 0, v___x_4202_);
                lean_ctor_set_uint8(
                    v___x_4204_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4203_,
                );
                v___x_4205_ = l_Repr_addAppParen(v___x_4204_, v_prec_4086_);
                return v___x_4205_;
            }
            18 => {
                v___x_4214_ = lean_unsigned_to_nat(1024);
                v___x_4230_ = lean_nat_dec_le(v___x_4214_, v_prec_4086_);
                if v___x_4230_ == 0 {
                    v___x_4231_ = lean_obj_once(
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
                    v___x_4232_ = lean_obj_once(
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
                v___x_4217_ = lean_box(1);
                v___x_4218_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__19;
                v___x_4219_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4209_, v___x_4214_);
                if v_isShared_4213_ == 0 {
                    lean_ctor_set(v___x_4212_, 1, v___x_4219_);
                    lean_ctor_set(v___x_4212_, 0, v___x_4218_);
                    v___x_4221_ = v___x_4212_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4218_);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4219_);
                    v___x_4221_ = v_reuseFailAlloc_4229_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_4222_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4222_, 0, v___x_4221_);
                lean_ctor_set(v___x_4222_, 1, v___x_4217_);
                v___x_4223_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_4210_, v___x_4214_);
                v___x_4224_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4224_, 0, v___x_4222_);
                lean_ctor_set(v___x_4224_, 1, v___x_4223_);
                lean_inc(v___y_4216_);
                v___x_4225_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4225_, 0, v___y_4216_);
                lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                v___x_4226_ = 0;
                v___x_4227_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4227_, 0, v___x_4225_);
                lean_ctor_set_uint8(
                    v___x_4227_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4226_,
                );
                v___x_4228_ = l_Repr_addAppParen(v___x_4227_, v_prec_4086_);
                return v___x_4228_;
            }
            21 => {
                v___x_4239_ = lean_unsigned_to_nat(1024);
                v___x_4255_ = lean_nat_dec_le(v___x_4239_, v_prec_4086_);
                if v___x_4255_ == 0 {
                    v___x_4256_ = lean_obj_once(
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
                    v___x_4257_ = lean_obj_once(
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
                v___x_4242_ = lean_box(1);
                v___x_4243_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__22;
                v___x_4244_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4234_, v___x_4239_);
                if v_isShared_4238_ == 0 {
                    lean_ctor_set_tag(v___x_4237_, 5);
                    lean_ctor_set(v___x_4237_, 1, v___x_4244_);
                    lean_ctor_set(v___x_4237_, 0, v___x_4243_);
                    v___x_4246_ = v___x_4237_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4243_);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 1, v___x_4244_);
                    v___x_4246_ = v_reuseFailAlloc_4254_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4247_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4247_, 0, v___x_4246_);
                lean_ctor_set(v___x_4247_, 1, v___x_4242_);
                v___x_4248_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_4235_, v___x_4239_);
                v___x_4249_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4249_, 0, v___x_4247_);
                lean_ctor_set(v___x_4249_, 1, v___x_4248_);
                lean_inc(v___y_4241_);
                v___x_4250_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4250_, 0, v___y_4241_);
                lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                v___x_4251_ = 0;
                v___x_4252_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4252_, 0, v___x_4250_);
                lean_ctor_set_uint8(
                    v___x_4252_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4251_,
                );
                v___x_4253_ = l_Repr_addAppParen(v___x_4252_, v_prec_4086_);
                return v___x_4253_;
            }
            24 => {
                v___x_4264_ = lean_unsigned_to_nat(1024);
                v___x_4280_ = lean_nat_dec_le(v___x_4264_, v_prec_4086_);
                if v___x_4280_ == 0 {
                    v___x_4281_ = lean_obj_once(
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
                    v___x_4282_ = lean_obj_once(
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
                v___x_4267_ = lean_box(1);
                v___x_4268_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__25;
                v___x_4269_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4259_, v___x_4264_);
                if v_isShared_4263_ == 0 {
                    lean_ctor_set_tag(v___x_4262_, 5);
                    lean_ctor_set(v___x_4262_, 1, v___x_4269_);
                    lean_ctor_set(v___x_4262_, 0, v___x_4268_);
                    v___x_4271_ = v___x_4262_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4268_);
                    lean_ctor_set(v_reuseFailAlloc_4279_, 1, v___x_4269_);
                    v___x_4271_ = v_reuseFailAlloc_4279_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4272_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4272_, 0, v___x_4271_);
                lean_ctor_set(v___x_4272_, 1, v___x_4267_);
                v___x_4273_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_4260_, v___x_4264_);
                v___x_4274_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4274_, 0, v___x_4272_);
                lean_ctor_set(v___x_4274_, 1, v___x_4273_);
                lean_inc(v___y_4266_);
                v___x_4275_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4275_, 0, v___y_4266_);
                lean_ctor_set(v___x_4275_, 1, v___x_4274_);
                v___x_4276_ = 0;
                v___x_4277_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4277_, 0, v___x_4275_);
                lean_ctor_set_uint8(
                    v___x_4277_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4276_,
                );
                v___x_4278_ = l_Repr_addAppParen(v___x_4277_, v_prec_4086_);
                return v___x_4278_;
            }
            27 => {
                v___x_4289_ = lean_unsigned_to_nat(1024);
                v___x_4306_ = lean_nat_dec_le(v___x_4289_, v_prec_4086_);
                if v___x_4306_ == 0 {
                    v___x_4307_ = lean_obj_once(
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
                    v___x_4308_ = lean_obj_once(
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
                v___x_4292_ = lean_box(1);
                v___x_4293_ = l_Lean_Grind_CommRing_instReprExpr_repr___closed__28;
                v___x_4294_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_4284_, v___x_4289_);
                if v_isShared_4288_ == 0 {
                    lean_ctor_set_tag(v___x_4287_, 5);
                    lean_ctor_set(v___x_4287_, 1, v___x_4294_);
                    lean_ctor_set(v___x_4287_, 0, v___x_4293_);
                    v___x_4296_ = v___x_4287_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4305_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4293_);
                    lean_ctor_set(v_reuseFailAlloc_4305_, 1, v___x_4294_);
                    v___x_4296_ = v_reuseFailAlloc_4305_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_4297_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4297_, 0, v___x_4296_);
                lean_ctor_set(v___x_4297_, 1, v___x_4292_);
                v___x_4298_ = l_Nat_reprFast(v_k_4285_);
                v___x_4299_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4299_, 0, v___x_4298_);
                v___x_4300_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4300_, 0, v___x_4297_);
                lean_ctor_set(v___x_4300_, 1, v___x_4299_);
                lean_inc(v___y_4291_);
                v___x_4301_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4301_, 0, v___y_4291_);
                lean_ctor_set(v___x_4301_, 1, v___x_4300_);
                v___x_4302_ = 0;
                v___x_4303_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4303_, 0, v___x_4301_);
                lean_ctor_set_uint8(
                    v___x_4303_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_4310_: *mut LeanObject,
    mut v_prec_4311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4312_: *mut LeanObject = core::ptr::null_mut();
    v_res_4312_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_x_4310_, v_prec_4311_);
    lean_dec(v_prec_4311_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote___redArg(
    mut v_ctx_4315_: *mut LeanObject,
    mut v_v_4316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    v___x_4317_ = l_Lean_RArray_getImpl___redArg(v_ctx_4315_, v_v_4316_);
    return v___x_4317_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote___redArg___boxed(
    mut v_ctx_4318_: *mut LeanObject,
    mut v_v_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4320_: *mut LeanObject = core::ptr::null_mut();
    v_res_4320_ = l_Lean_Grind_CommRing_Var_denote___redArg(v_ctx_4318_, v_v_4319_);
    lean_dec(v_v_4319_);
    lean_dec_ref(v_ctx_4318_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote(
    mut v_00_u03b1_4321_: *mut LeanObject,
    mut v_ctx_4322_: *mut LeanObject,
    mut v_v_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    v___x_4324_ = l_Lean_RArray_getImpl___redArg(v_ctx_4322_, v_v_4323_);
    return v___x_4324_;
}
pub unsafe fn l_Lean_Grind_CommRing_Var_denote___boxed(
    mut v_00_u03b1_4325_: *mut LeanObject,
    mut v_ctx_4326_: *mut LeanObject,
    mut v_v_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4328_: *mut LeanObject = core::ptr::null_mut();
    v_res_4328_ = l_Lean_Grind_CommRing_Var_denote(v_00_u03b1_4325_, v_ctx_4326_, v_v_4327_);
    lean_dec(v_v_4327_);
    lean_dec_ref(v_ctx_4326_);
    return v_res_4328_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqPower_beq(
    mut v_x_4329_: *mut LeanObject,
    mut v_x_4330_: *mut LeanObject,
) -> u8 {
    let mut v_x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    v_x_4331_ = lean_ctor_get(v_x_4329_, 0);
    v_k_4332_ = lean_ctor_get(v_x_4329_, 1);
    v_x_4333_ = lean_ctor_get(v_x_4330_, 0);
    v_k_4334_ = lean_ctor_get(v_x_4330_, 1);
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
    mut v_x_4337_: *mut LeanObject,
    mut v_x_4338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4339_: u8 = 0;
    let mut v_r_4340_: *mut LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_x_4337_, v_x_4338_);
    lean_dec_ref(v_x_4338_);
    lean_dec_ref(v_x_4337_);
    v_r_4340_ = lean_box((v_res_4339_) as usize);
    return v_r_4340_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(
    mut v_x_4343_: *mut LeanObject,
    mut v_x_4344_: *mut LeanObject,
    mut v_h__1_4345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    v_x_4346_ = lean_ctor_get(v_x_4343_, 0);
    lean_inc(v_x_4346_);
    v_k_4347_ = lean_ctor_get(v_x_4343_, 1);
    lean_inc(v_k_4347_);
    lean_dec_ref(v_x_4343_);
    v_x_4348_ = lean_ctor_get(v_x_4344_, 0);
    lean_inc(v_x_4348_);
    v_k_4349_ = lean_ctor_get(v_x_4344_, 1);
    lean_inc(v_k_4349_);
    lean_dec_ref(v_x_4344_);
    v___x_4350_ = lean_apply_4(v_h__1_4345_, v_x_4346_, v_k_4347_, v_x_4348_, v_k_4349_);
    return v___x_4350_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(
    mut v_motive_4351_: *mut LeanObject,
    mut v_x_4352_: *mut LeanObject,
    mut v_x_4353_: *mut LeanObject,
    mut v_h__1_4354_: *mut LeanObject,
    mut v_h__2_4355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    v_x_4356_ = lean_ctor_get(v_x_4352_, 0);
    lean_inc(v_x_4356_);
    v_k_4357_ = lean_ctor_get(v_x_4352_, 1);
    lean_inc(v_k_4357_);
    lean_dec_ref(v_x_4352_);
    v_x_4358_ = lean_ctor_get(v_x_4353_, 0);
    lean_inc(v_x_4358_);
    v_k_4359_ = lean_ctor_get(v_x_4353_, 1);
    lean_inc(v_k_4359_);
    lean_dec_ref(v_x_4353_);
    v___x_4360_ = lean_apply_4(v_h__1_4354_, v_x_4356_, v_k_4357_, v_x_4358_, v_k_4359_);
    return v___x_4360_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(
    mut v_motive_4361_: *mut LeanObject,
    mut v_x_4362_: *mut LeanObject,
    mut v_x_4363_: *mut LeanObject,
    mut v_h__1_4364_: *mut LeanObject,
    mut v_h__2_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4366_: *mut LeanObject = core::ptr::null_mut();
    v_res_4366_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(v_motive_4361_, v_x_4362_, v_x_4363_, v_h__1_4364_, v_h__2_4365_);
    lean_dec(v_h__2_4365_);
    return v_res_4366_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(
    mut v_a_4367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = lean_nat_to_int(v_a_4367_);
    return v___x_4368_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    v___x_4382_ = lean_unsigned_to_nat(5);
    v___x_4383_ = lean_nat_to_int(v___x_4382_);
    return v___x_4383_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    v___x_4391_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0;
    v___x_4392_ = lean_string_length(v___x_4391_);
    return v___x_4392_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    v___x_4393_ = lean_obj_once(
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
    mut v_x_4399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_4400_ = lean_ctor_get(v_x_4399_, 0);
                v_k_4401_ = lean_ctor_get(v_x_4399_, 1);
                v_isSharedCheck_4435_ = (!lean_is_exclusive(v_x_4399_)) as u8;
                if v_isSharedCheck_4435_ == 0 {
                    v___x_4403_ = v_x_4399_;
                    v_isShared_4404_ = v_isSharedCheck_4435_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_k_4401_);
                    lean_inc(v_x_4400_);
                    lean_dec(v_x_4399_);
                    v___x_4403_ = lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5;
                v___x_4406_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6;
                v___x_4407_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7,
                );
                v___x_4408_ = l_Nat_reprFast(v_x_4400_);
                v___x_4409_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4409_, 0, v___x_4408_);
                if v_isShared_4404_ == 0 {
                    lean_ctor_set_tag(v___x_4403_, 4);
                    lean_ctor_set(v___x_4403_, 1, v___x_4409_);
                    lean_ctor_set(v___x_4403_, 0, v___x_4407_);
                    v___x_4411_ = v___x_4403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4407_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 1, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4412_ = 0;
                v___x_4413_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4413_, 0, v___x_4411_);
                lean_ctor_set_uint8(
                    v___x_4413_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4412_,
                );
                v___x_4414_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4414_, 0, v___x_4406_);
                lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9;
                v___x_4416_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4416_, 0, v___x_4414_);
                lean_ctor_set(v___x_4416_, 1, v___x_4415_);
                v___x_4417_ = lean_box(1);
                v___x_4418_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4418_, 0, v___x_4416_);
                lean_ctor_set(v___x_4418_, 1, v___x_4417_);
                v___x_4419_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11;
                v___x_4420_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4420_, 0, v___x_4418_);
                lean_ctor_set(v___x_4420_, 1, v___x_4419_);
                v___x_4421_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4421_, 0, v___x_4420_);
                lean_ctor_set(v___x_4421_, 1, v___x_4405_);
                v___x_4422_ = l_Nat_reprFast(v_k_4401_);
                v___x_4423_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4423_, 0, v___x_4422_);
                v___x_4424_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4424_, 0, v___x_4407_);
                lean_ctor_set(v___x_4424_, 1, v___x_4423_);
                v___x_4425_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4425_, 0, v___x_4424_);
                lean_ctor_set_uint8(
                    v___x_4425_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4412_,
                );
                v___x_4426_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4426_, 0, v___x_4421_);
                lean_ctor_set(v___x_4426_, 1, v___x_4425_);
                v___x_4427_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once
                    ),
                    _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14,
                );
                v___x_4428_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15;
                v___x_4429_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4429_, 0, v___x_4428_);
                lean_ctor_set(v___x_4429_, 1, v___x_4426_);
                v___x_4430_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16;
                v___x_4431_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4431_, 0, v___x_4429_);
                lean_ctor_set(v___x_4431_, 1, v___x_4430_);
                v___x_4432_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4432_, 0, v___x_4427_);
                lean_ctor_set(v___x_4432_, 1, v___x_4431_);
                v___x_4433_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4433_, 0, v___x_4432_);
                lean_ctor_set_uint8(
                    v___x_4433_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4412_,
                );
                return v___x_4433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPower_repr(
    mut v_x_4436_: *mut LeanObject,
    mut v_prec_4437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    v___x_4438_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_x_4436_);
    return v___x_4438_;
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPower_repr___boxed(
    mut v_x_4439_: *mut LeanObject,
    mut v_prec_4440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4441_: *mut LeanObject = core::ptr::null_mut();
    v_res_4441_ = l_Lean_Grind_CommRing_instReprPower_repr(v_x_4439_, v_prec_4440_);
    lean_dec(v_prec_4440_);
    return v_res_4441_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePower_hash(mut v_x_4448_: *mut LeanObject) -> u64 {
    let mut v_x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u64 = 0;
    let mut v___x_4452_: u64 = 0;
    let mut v___x_4453_: u64 = 0;
    let mut v___x_4454_: u64 = 0;
    let mut v___x_4455_: u64 = 0;
    v_x_4449_ = lean_ctor_get(v_x_4448_, 0);
    v_k_4450_ = lean_ctor_get(v_x_4448_, 1);
    v___x_4451_ = 0u64;
    v___x_4452_ = lean_uint64_of_nat(v_x_4449_);
    v___x_4453_ = lean_uint64_mix_hash(v___x_4451_, v___x_4452_);
    v___x_4454_ = lean_uint64_of_nat(v_k_4450_);
    v___x_4455_ = lean_uint64_mix_hash(v___x_4453_, v___x_4454_);
    return v___x_4455_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePower_hash___boxed(
    mut v_x_4456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4457_: u64 = 0;
    let mut v_r_4458_: *mut LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_4456_);
    lean_dec_ref(v_x_4456_);
    v_r_4458_ = lean_box_uint64(v_res_4457_);
    return v_r_4458_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_varLt(
    mut v_p_u2081_4461_: *mut LeanObject,
    mut v_p_u2082_4462_: *mut LeanObject,
) -> u8 {
    let mut v_x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    v_x_4463_ = lean_ctor_get(v_p_u2081_4461_, 0);
    v_x_4464_ = lean_ctor_get(v_p_u2082_4462_, 0);
    v___x_4465_ = l_Nat_blt(v_x_4463_, v_x_4464_);
    return v___x_4465_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_varLt___boxed(
    mut v_p_u2081_4466_: *mut LeanObject,
    mut v_p_u2082_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4468_: u8 = 0;
    let mut v_r_4469_: *mut LeanObject = core::ptr::null_mut();
    v_res_4468_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_4466_, v_p_u2082_4467_);
    lean_dec_ref(v_p_u2082_4467_);
    lean_dec_ref(v_p_u2081_4466_);
    v_r_4469_ = lean_box((v_res_4468_) as usize);
    return v_r_4469_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote___redArg(
    mut v_inst_4470_: *mut LeanObject,
    mut v_ctx_4471_: *mut LeanObject,
    mut v_x_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofNat_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    v_ofNat_4473_ = lean_ctor_get(v_inst_4470_, 3);
    lean_inc(v_ofNat_4473_);
    v_npow_4474_ = lean_ctor_get(v_inst_4470_, 5);
    lean_inc(v_npow_4474_);
    lean_dec_ref(v_inst_4470_);
    v_x_4475_ = lean_ctor_get(v_x_4472_, 0);
    lean_inc(v_x_4475_);
    v_k_4476_ = lean_ctor_get(v_x_4472_, 1);
    lean_inc(v_k_4476_);
    lean_dec_ref(v_x_4472_);
    v___x_4477_ = lean_unsigned_to_nat(0);
    v___x_4478_ = lean_nat_dec_eq(v_k_4476_, v___x_4477_);
    if v___x_4478_ == 0 {
        let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4480_: u8 = 0;
        lean_dec(v_ofNat_4473_);
        v___x_4479_ = lean_unsigned_to_nat(1);
        v___x_4480_ = lean_nat_dec_eq(v_k_4476_, v___x_4479_);
        if v___x_4480_ == 0 {
            let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
            v___x_4481_ = l_Lean_RArray_getImpl___redArg(v_ctx_4471_, v_x_4475_);
            lean_dec(v_x_4475_);
            v___x_4482_ = lean_apply_2(v_npow_4474_, v___x_4481_, v_k_4476_);
            return v___x_4482_;
        } else {
            let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_4476_);
            lean_dec(v_npow_4474_);
            v___x_4483_ = l_Lean_RArray_getImpl___redArg(v_ctx_4471_, v_x_4475_);
            lean_dec(v_x_4475_);
            return v___x_4483_;
        }
    } else {
        let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_4476_);
        lean_dec(v_x_4475_);
        lean_dec(v_npow_4474_);
        v___x_4484_ = lean_unsigned_to_nat(1);
        v___x_4485_ = lean_apply_1(v_ofNat_4473_, v___x_4484_);
        return v___x_4485_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote___redArg___boxed(
    mut v_inst_4486_: *mut LeanObject,
    mut v_ctx_4487_: *mut LeanObject,
    mut v_x_4488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4489_: *mut LeanObject = core::ptr::null_mut();
    v_res_4489_ = l_Lean_Grind_CommRing_Power_denote___redArg(v_inst_4486_, v_ctx_4487_, v_x_4488_);
    lean_dec_ref(v_ctx_4487_);
    return v_res_4489_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote(
    mut v_00_u03b1_4490_: *mut LeanObject,
    mut v_inst_4491_: *mut LeanObject,
    mut v_ctx_4492_: *mut LeanObject,
    mut v_x_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofNat_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    v_ofNat_4494_ = lean_ctor_get(v_inst_4491_, 3);
    lean_inc(v_ofNat_4494_);
    v_npow_4495_ = lean_ctor_get(v_inst_4491_, 5);
    lean_inc(v_npow_4495_);
    lean_dec_ref(v_inst_4491_);
    v_x_4496_ = lean_ctor_get(v_x_4493_, 0);
    lean_inc(v_x_4496_);
    v_k_4497_ = lean_ctor_get(v_x_4493_, 1);
    lean_inc(v_k_4497_);
    lean_dec_ref(v_x_4493_);
    v___x_4498_ = lean_unsigned_to_nat(0);
    v___x_4499_ = lean_nat_dec_eq(v_k_4497_, v___x_4498_);
    if v___x_4499_ == 0 {
        let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4501_: u8 = 0;
        lean_dec(v_ofNat_4494_);
        v___x_4500_ = lean_unsigned_to_nat(1);
        v___x_4501_ = lean_nat_dec_eq(v_k_4497_, v___x_4500_);
        if v___x_4501_ == 0 {
            let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
            v___x_4502_ = l_Lean_RArray_getImpl___redArg(v_ctx_4492_, v_x_4496_);
            lean_dec(v_x_4496_);
            v___x_4503_ = lean_apply_2(v_npow_4495_, v___x_4502_, v_k_4497_);
            return v___x_4503_;
        } else {
            let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_4497_);
            lean_dec(v_npow_4495_);
            v___x_4504_ = l_Lean_RArray_getImpl___redArg(v_ctx_4492_, v_x_4496_);
            lean_dec(v_x_4496_);
            return v___x_4504_;
        }
    } else {
        let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_4497_);
        lean_dec(v_x_4496_);
        lean_dec(v_npow_4495_);
        v___x_4505_ = lean_unsigned_to_nat(1);
        v___x_4506_ = lean_apply_1(v_ofNat_4494_, v___x_4505_);
        return v___x_4506_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denote___boxed(
    mut v_00_u03b1_4507_: *mut LeanObject,
    mut v_inst_4508_: *mut LeanObject,
    mut v_ctx_4509_: *mut LeanObject,
    mut v_x_4510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4511_: *mut LeanObject = core::ptr::null_mut();
    v_res_4511_ =
        l_Lean_Grind_CommRing_Power_denote(v_00_u03b1_4507_, v_inst_4508_, v_ctx_4509_, v_x_4510_);
    lean_dec_ref(v_ctx_4509_);
    return v_res_4511_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorIdx(mut v_x_4512_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_4512_) == 0 {
        let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
        v___x_4513_ = lean_unsigned_to_nat(0);
        return v___x_4513_;
    } else {
        let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
        v___x_4514_ = lean_unsigned_to_nat(1);
        return v___x_4514_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorIdx___boxed(
    mut v_x_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4516_: *mut LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_Grind_CommRing_Mon_ctorIdx(v_x_4515_);
    lean_dec(v_x_4515_);
    return v_res_4516_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorElim___redArg(
    mut v_t_4517_: *mut LeanObject,
    mut v_k_4518_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4517_) == 0 {
        return v_k_4518_;
    } else {
        let mut v_p_4519_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_4520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
        v_p_4519_ = lean_ctor_get(v_t_4517_, 0);
        lean_inc_ref(v_p_4519_);
        v_m_4520_ = lean_ctor_get(v_t_4517_, 1);
        lean_inc(v_m_4520_);
        lean_dec_ref_known(v_t_4517_, 2);
        v___x_4521_ = lean_apply_2(v_k_4518_, v_p_4519_, v_m_4520_);
        return v___x_4521_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorElim(
    mut v_motive_4522_: *mut LeanObject,
    mut v_ctorIdx_4523_: *mut LeanObject,
    mut v_t_4524_: *mut LeanObject,
    mut v_h_4525_: *mut LeanObject,
    mut v_k_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    v___x_4527_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4524_, v_k_4526_);
    return v___x_4527_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ctorElim___boxed(
    mut v_motive_4528_: *mut LeanObject,
    mut v_ctorIdx_4529_: *mut LeanObject,
    mut v_t_4530_: *mut LeanObject,
    mut v_h_4531_: *mut LeanObject,
    mut v_k_4532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4533_: *mut LeanObject = core::ptr::null_mut();
    v_res_4533_ = l_Lean_Grind_CommRing_Mon_ctorElim(
        v_motive_4528_,
        v_ctorIdx_4529_,
        v_t_4530_,
        v_h_4531_,
        v_k_4532_,
    );
    lean_dec(v_ctorIdx_4529_);
    return v_res_4533_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_unit_elim___redArg(
    mut v_t_4534_: *mut LeanObject,
    mut v_unit_4535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    v___x_4536_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4534_, v_unit_4535_);
    return v___x_4536_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_unit_elim(
    mut v_motive_4537_: *mut LeanObject,
    mut v_t_4538_: *mut LeanObject,
    mut v_h_4539_: *mut LeanObject,
    mut v_unit_4540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    v___x_4541_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4538_, v_unit_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mult_elim___redArg(
    mut v_t_4542_: *mut LeanObject,
    mut v_mult_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    v___x_4544_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4542_, v_mult_4543_);
    return v___x_4544_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mult_elim(
    mut v_motive_4545_: *mut LeanObject,
    mut v_t_4546_: *mut LeanObject,
    mut v_h_4547_: *mut LeanObject,
    mut v_mult_4548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    v___x_4549_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_4546_, v_mult_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqMon_beq(
    mut v_x_4550_: *mut LeanObject,
    mut v_x_4551_: *mut LeanObject,
) -> u8 {
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: u8 = 0;
    let mut v_p_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4550_) == 0 {
                    if lean_obj_tag(v_x_4551_) == 0 {
                        v___x_4552_ = 1;
                        return v___x_4552_;
                    } else {
                        v___x_4553_ = 0;
                        return v___x_4553_;
                    }
                } else {
                    if lean_obj_tag(v_x_4551_) == 1 {
                        v_p_4554_ = lean_ctor_get(v_x_4550_, 0);
                        v_m_4555_ = lean_ctor_get(v_x_4550_, 1);
                        v_p_4556_ = lean_ctor_get(v_x_4551_, 0);
                        v_m_4557_ = lean_ctor_get(v_x_4551_, 1);
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
    mut v_x_4561_: *mut LeanObject,
    mut v_x_4562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4563_: u8 = 0;
    let mut v_r_4564_: *mut LeanObject = core::ptr::null_mut();
    v_res_4563_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_4561_, v_x_4562_);
    lean_dec(v_x_4562_);
    lean_dec(v_x_4561_);
    v_r_4564_ = lean_box((v_res_4563_) as usize);
    return v_r_4564_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(
    mut v_x_4567_: *mut LeanObject,
    mut v_x_4568_: *mut LeanObject,
    mut v_h__1_4569_: *mut LeanObject,
    mut v_h__2_4570_: *mut LeanObject,
    mut v_h__3_4571_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4567_) == 0 {
        lean_dec(v_h__2_4570_);
        if lean_obj_tag(v_x_4568_) == 0 {
            let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4571_);
            v___x_4572_ = lean_box(0);
            v___x_4573_ = lean_apply_1(v_h__1_4569_, v___x_4572_);
            return v___x_4573_;
        } else {
            let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_4569_);
            v___x_4574_ =
                lean_apply_4(v_h__3_4571_, v_x_4567_, v_x_4568_, lean_box(0), lean_box(0));
            return v___x_4574_;
        }
    } else {
        lean_dec(v_h__1_4569_);
        if lean_obj_tag(v_x_4568_) == 1 {
            let mut v_p_4575_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_4576_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_4577_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_4578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4571_);
            v_p_4575_ = lean_ctor_get(v_x_4567_, 0);
            lean_inc_ref(v_p_4575_);
            v_m_4576_ = lean_ctor_get(v_x_4567_, 1);
            lean_inc(v_m_4576_);
            lean_dec_ref_known(v_x_4567_, 2);
            v_p_4577_ = lean_ctor_get(v_x_4568_, 0);
            lean_inc_ref(v_p_4577_);
            v_m_4578_ = lean_ctor_get(v_x_4568_, 1);
            lean_inc(v_m_4578_);
            lean_dec_ref_known(v_x_4568_, 2);
            v___x_4579_ = lean_apply_4(v_h__2_4570_, v_p_4575_, v_m_4576_, v_p_4577_, v_m_4578_);
            return v___x_4579_;
        } else {
            let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_4570_);
            v___x_4580_ =
                lean_apply_4(v_h__3_4571_, v_x_4567_, v_x_4568_, lean_box(0), lean_box(0));
            return v___x_4580_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(
    mut v_motive_4581_: *mut LeanObject,
    mut v_x_4582_: *mut LeanObject,
    mut v_x_4583_: *mut LeanObject,
    mut v_h__1_4584_: *mut LeanObject,
    mut v_h__2_4585_: *mut LeanObject,
    mut v_h__3_4586_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4582_) == 0 {
        lean_dec(v_h__2_4585_);
        if lean_obj_tag(v_x_4583_) == 0 {
            let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4586_);
            v___x_4587_ = lean_box(0);
            v___x_4588_ = lean_apply_1(v_h__1_4584_, v___x_4587_);
            return v___x_4588_;
        } else {
            let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_4584_);
            v___x_4589_ =
                lean_apply_4(v_h__3_4586_, v_x_4582_, v_x_4583_, lean_box(0), lean_box(0));
            return v___x_4589_;
        }
    } else {
        lean_dec(v_h__1_4584_);
        if lean_obj_tag(v_x_4583_) == 1 {
            let mut v_p_4590_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_4591_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_4592_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_4593_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4586_);
            v_p_4590_ = lean_ctor_get(v_x_4582_, 0);
            lean_inc_ref(v_p_4590_);
            v_m_4591_ = lean_ctor_get(v_x_4582_, 1);
            lean_inc(v_m_4591_);
            lean_dec_ref_known(v_x_4582_, 2);
            v_p_4592_ = lean_ctor_get(v_x_4583_, 0);
            lean_inc_ref(v_p_4592_);
            v_m_4593_ = lean_ctor_get(v_x_4583_, 1);
            lean_inc(v_m_4593_);
            lean_dec_ref_known(v_x_4583_, 2);
            v___x_4594_ = lean_apply_4(v_h__2_4585_, v_p_4590_, v_m_4591_, v_p_4592_, v_m_4593_);
            return v___x_4594_;
        } else {
            let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_4585_);
            v___x_4595_ =
                lean_apply_4(v_h__3_4586_, v_x_4582_, v_x_4583_, lean_box(0), lean_box(0));
            return v___x_4595_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprMon_repr(
    mut v_x_4605_: *mut LeanObject,
    mut v_prec_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: u8 = 0;
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: u8 = 0;
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4605_) == 0 {
                    v___x_4614_ = lean_unsigned_to_nat(1024);
                    v___x_4615_ = lean_nat_dec_le(v___x_4614_, v_prec_4606_);
                    if v___x_4615_ == 0 {
                        v___x_4616_ = lean_obj_once(
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
                        v___x_4617_ = lean_obj_once(
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
                    v_p_4618_ = lean_ctor_get(v_x_4605_, 0);
                    v_m_4619_ = lean_ctor_get(v_x_4605_, 1);
                    v_isSharedCheck_4642_ = (!lean_is_exclusive(v_x_4605_)) as u8;
                    if v_isSharedCheck_4642_ == 0 {
                        v___x_4621_ = v_x_4605_;
                        v_isShared_4622_ = v_isSharedCheck_4642_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_m_4619_);
                        lean_inc(v_p_4618_);
                        lean_dec(v_x_4605_);
                        v___x_4621_ = lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4642_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4609_ = l_Lean_Grind_CommRing_instReprMon_repr___closed__1;
                lean_inc(v___y_4608_);
                v___x_4610_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4610_, 0, v___y_4608_);
                lean_ctor_set(v___x_4610_, 1, v___x_4609_);
                v___x_4611_ = 0;
                v___x_4612_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4612_, 0, v___x_4610_);
                lean_ctor_set_uint8(
                    v___x_4612_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4611_,
                );
                v___x_4613_ = l_Repr_addAppParen(v___x_4612_, v_prec_4606_);
                return v___x_4613_;
            }
            2 => {
                v___x_4623_ = lean_unsigned_to_nat(1024);
                v___x_4639_ = lean_nat_dec_le(v___x_4623_, v_prec_4606_);
                if v___x_4639_ == 0 {
                    v___x_4640_ = lean_obj_once(
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
                    v___x_4641_ = lean_obj_once(
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
                v___x_4626_ = lean_box(1);
                v___x_4627_ = l_Lean_Grind_CommRing_instReprMon_repr___closed__4;
                v___x_4628_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_p_4618_);
                if v_isShared_4622_ == 0 {
                    lean_ctor_set_tag(v___x_4621_, 5);
                    lean_ctor_set(v___x_4621_, 1, v___x_4628_);
                    lean_ctor_set(v___x_4621_, 0, v___x_4627_);
                    v___x_4630_ = v___x_4621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4627_);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4628_);
                    v___x_4630_ = v_reuseFailAlloc_4638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4631_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4631_, 0, v___x_4630_);
                lean_ctor_set(v___x_4631_, 1, v___x_4626_);
                v___x_4632_ = l_Lean_Grind_CommRing_instReprMon_repr(v_m_4619_, v___x_4623_);
                v___x_4633_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4633_, 0, v___x_4631_);
                lean_ctor_set(v___x_4633_, 1, v___x_4632_);
                lean_inc(v___y_4625_);
                v___x_4634_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4634_, 0, v___y_4625_);
                lean_ctor_set(v___x_4634_, 1, v___x_4633_);
                v___x_4635_ = 0;
                v___x_4636_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4636_, 0, v___x_4634_);
                lean_ctor_set_uint8(
                    v___x_4636_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_4643_: *mut LeanObject,
    mut v_prec_4644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4645_: *mut LeanObject = core::ptr::null_mut();
    v_res_4645_ = l_Lean_Grind_CommRing_instReprMon_repr(v_x_4643_, v_prec_4644_);
    lean_dec(v_prec_4644_);
    return v_res_4645_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedMon_default() -> *mut LeanObject {
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    v___x_4648_ = lean_box(0);
    return v___x_4648_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedMon() -> *mut LeanObject {
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    v___x_4649_ = lean_box(0);
    return v___x_4649_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableMon_hash(mut v_x_4650_: *mut LeanObject) -> u64 {
    if lean_obj_tag(v_x_4650_) == 0 {
        let mut v___x_4651_: u64 = 0;
        v___x_4651_ = 0u64;
        return v___x_4651_;
    } else {
        let mut v_p_4652_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_4653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4654_: u64 = 0;
        let mut v___x_4655_: u64 = 0;
        let mut v___x_4656_: u64 = 0;
        let mut v___x_4657_: u64 = 0;
        let mut v___x_4658_: u64 = 0;
        v_p_4652_ = lean_ctor_get(v_x_4650_, 0);
        v_m_4653_ = lean_ctor_get(v_x_4650_, 1);
        v___x_4654_ = 1u64;
        v___x_4655_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_p_4652_);
        v___x_4656_ = lean_uint64_mix_hash(v___x_4654_, v___x_4655_);
        v___x_4657_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_m_4653_);
        v___x_4658_ = lean_uint64_mix_hash(v___x_4656_, v___x_4657_);
        return v___x_4658_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instHashableMon_hash___boxed(
    mut v_x_4659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4660_: u64 = 0;
    let mut v_r_4661_: *mut LeanObject = core::ptr::null_mut();
    v_res_4660_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_4659_);
    lean_dec(v_x_4659_);
    v_r_4661_ = lean_box_uint64(v_res_4660_);
    return v_r_4661_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote___redArg(
    mut v_inst_4664_: *mut LeanObject,
    mut v_ctx_4665_: *mut LeanObject,
    mut v_x_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofNat_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMul_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNat_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4666_) == 0 {
                    v_ofNat_4667_ = lean_ctor_get(v_inst_4664_, 3);
                    lean_inc(v_ofNat_4667_);
                    lean_dec_ref(v_inst_4664_);
                    v___x_4668_ = lean_unsigned_to_nat(1);
                    v___x_4669_ = lean_apply_1(v_ofNat_4667_, v___x_4668_);
                    return v___x_4669_;
                } else {
                    v_toMul_4670_ = lean_ctor_get(v_inst_4664_, 1);
                    lean_inc(v_toMul_4670_);
                    v_ofNat_4671_ = lean_ctor_get(v_inst_4664_, 3);
                    v_npow_4672_ = lean_ctor_get(v_inst_4664_, 5);
                    v_p_4673_ = lean_ctor_get(v_x_4666_, 0);
                    lean_inc_ref(v_p_4673_);
                    v_m_4674_ = lean_ctor_get(v_x_4666_, 1);
                    lean_inc(v_m_4674_);
                    lean_dec_ref_known(v_x_4666_, 2);
                    v_x_4679_ = lean_ctor_get(v_p_4673_, 0);
                    lean_inc(v_x_4679_);
                    v_k_4680_ = lean_ctor_get(v_p_4673_, 1);
                    lean_inc(v_k_4680_);
                    lean_dec_ref(v_p_4673_);
                    v___x_4681_ = lean_unsigned_to_nat(0);
                    v___x_4682_ = lean_nat_dec_eq(v_k_4680_, v___x_4681_);
                    if v___x_4682_ == 0 {
                        v___x_4683_ = lean_unsigned_to_nat(1);
                        v___x_4684_ = lean_nat_dec_eq(v_k_4680_, v___x_4683_);
                        if v___x_4684_ == 0 {
                            v___x_4685_ = l_Lean_RArray_getImpl___redArg(v_ctx_4665_, v_x_4679_);
                            lean_dec(v_x_4679_);
                            lean_inc(v_npow_4672_);
                            v___x_4686_ = lean_apply_2(v_npow_4672_, v___x_4685_, v_k_4680_);
                            v___y_4676_ = v___x_4686_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_k_4680_);
                            v___x_4687_ = l_Lean_RArray_getImpl___redArg(v_ctx_4665_, v_x_4679_);
                            lean_dec(v_x_4679_);
                            v___y_4676_ = v___x_4687_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_4680_);
                        lean_dec(v_x_4679_);
                        v___x_4688_ = lean_unsigned_to_nat(1);
                        lean_inc(v_ofNat_4671_);
                        v___x_4689_ = lean_apply_1(v_ofNat_4671_, v___x_4688_);
                        v___y_4676_ = v___x_4689_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4677_ =
                    l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_4664_, v_ctx_4665_, v_m_4674_);
                v___x_4678_ = lean_apply_2(v_toMul_4670_, v___y_4676_, v___x_4677_);
                return v___x_4678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(
    mut v_inst_4690_: *mut LeanObject,
    mut v_ctx_4691_: *mut LeanObject,
    mut v_x_4692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4693_: *mut LeanObject = core::ptr::null_mut();
    v_res_4693_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_4690_, v_ctx_4691_, v_x_4692_);
    lean_dec_ref(v_ctx_4691_);
    return v_res_4693_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote(
    mut v_00_u03b1_4694_: *mut LeanObject,
    mut v_inst_4695_: *mut LeanObject,
    mut v_ctx_4696_: *mut LeanObject,
    mut v_x_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_4695_, v_ctx_4696_, v_x_4697_);
    return v___x_4698_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote___boxed(
    mut v_00_u03b1_4699_: *mut LeanObject,
    mut v_inst_4700_: *mut LeanObject,
    mut v_ctx_4701_: *mut LeanObject,
    mut v_x_4702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4703_: *mut LeanObject = core::ptr::null_mut();
    v_res_4703_ =
        l_Lean_Grind_CommRing_Mon_denote(v_00_u03b1_4699_, v_inst_4700_, v_ctx_4701_, v_x_4702_);
    lean_dec_ref(v_ctx_4701_);
    return v_res_4703_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
    mut v_inst_4704_: *mut LeanObject,
    mut v_ctx_4705_: *mut LeanObject,
    mut v_m_4706_: *mut LeanObject,
    mut v_acc_4707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMul_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNat_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: u8 = 0;
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_4706_) == 0 {
                    lean_dec_ref(v_inst_4704_);
                    return v_acc_4707_;
                } else {
                    v_toMul_4708_ = lean_ctor_get(v_inst_4704_, 1);
                    v_ofNat_4709_ = lean_ctor_get(v_inst_4704_, 3);
                    v_npow_4710_ = lean_ctor_get(v_inst_4704_, 5);
                    v_p_4711_ = lean_ctor_get(v_m_4706_, 0);
                    lean_inc_ref(v_p_4711_);
                    v_m_4712_ = lean_ctor_get(v_m_4706_, 1);
                    lean_inc(v_m_4712_);
                    lean_dec_ref_known(v_m_4706_, 2);
                    v_x_4717_ = lean_ctor_get(v_p_4711_, 0);
                    lean_inc(v_x_4717_);
                    v_k_4718_ = lean_ctor_get(v_p_4711_, 1);
                    lean_inc(v_k_4718_);
                    lean_dec_ref(v_p_4711_);
                    v___x_4719_ = lean_unsigned_to_nat(0);
                    v___x_4720_ = lean_nat_dec_eq(v_k_4718_, v___x_4719_);
                    if v___x_4720_ == 0 {
                        v___x_4721_ = lean_unsigned_to_nat(1);
                        v___x_4722_ = lean_nat_dec_eq(v_k_4718_, v___x_4721_);
                        if v___x_4722_ == 0 {
                            v___x_4723_ = l_Lean_RArray_getImpl___redArg(v_ctx_4705_, v_x_4717_);
                            lean_dec(v_x_4717_);
                            lean_inc(v_npow_4710_);
                            v___x_4724_ = lean_apply_2(v_npow_4710_, v___x_4723_, v_k_4718_);
                            v___y_4714_ = v___x_4724_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_k_4718_);
                            v___x_4725_ = l_Lean_RArray_getImpl___redArg(v_ctx_4705_, v_x_4717_);
                            lean_dec(v_x_4717_);
                            v___y_4714_ = v___x_4725_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_4718_);
                        lean_dec(v_x_4717_);
                        v___x_4726_ = lean_unsigned_to_nat(1);
                        lean_inc(v_ofNat_4709_);
                        v___x_4727_ = lean_apply_1(v_ofNat_4709_, v___x_4726_);
                        v___y_4714_ = v___x_4727_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_toMul_4708_);
                v___x_4715_ = lean_apply_2(v_toMul_4708_, v_acc_4707_, v___y_4714_);
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
    mut v_inst_4728_: *mut LeanObject,
    mut v_ctx_4729_: *mut LeanObject,
    mut v_m_4730_: *mut LeanObject,
    mut v_acc_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4732_: *mut LeanObject = core::ptr::null_mut();
    v_res_4732_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
        v_inst_4728_,
        v_ctx_4729_,
        v_m_4730_,
        v_acc_4731_,
    );
    lean_dec_ref(v_ctx_4729_);
    return v_res_4732_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go(
    mut v_00_u03b1_4733_: *mut LeanObject,
    mut v_inst_4734_: *mut LeanObject,
    mut v_ctx_4735_: *mut LeanObject,
    mut v_m_4736_: *mut LeanObject,
    mut v_acc_4737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    v___x_4738_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
        v_inst_4734_,
        v_ctx_4735_,
        v_m_4736_,
        v_acc_4737_,
    );
    return v___x_4738_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(
    mut v_00_u03b1_4739_: *mut LeanObject,
    mut v_inst_4740_: *mut LeanObject,
    mut v_ctx_4741_: *mut LeanObject,
    mut v_m_4742_: *mut LeanObject,
    mut v_acc_4743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4744_: *mut LeanObject = core::ptr::null_mut();
    v_res_4744_ = l_Lean_Grind_CommRing_Mon_denote_x27_go(
        v_00_u03b1_4739_,
        v_inst_4740_,
        v_ctx_4741_,
        v_m_4742_,
        v_acc_4743_,
    );
    lean_dec_ref(v_ctx_4741_);
    return v_res_4744_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27___redArg(
    mut v_inst_4745_: *mut LeanObject,
    mut v_ctx_4746_: *mut LeanObject,
    mut v_m_4747_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_4747_) == 0 {
        let mut v_ofNat_4748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
        v_ofNat_4748_ = lean_ctor_get(v_inst_4745_, 3);
        lean_inc(v_ofNat_4748_);
        lean_dec_ref(v_inst_4745_);
        v___x_4749_ = lean_unsigned_to_nat(1);
        v___x_4750_ = lean_apply_1(v_ofNat_4748_, v___x_4749_);
        return v___x_4750_;
    } else {
        let mut v_p_4751_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_4752_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_4753_: *mut LeanObject = core::ptr::null_mut();
        let mut v_npow_4754_: *mut LeanObject = core::ptr::null_mut();
        let mut v_x_4755_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4758_: u8 = 0;
        v_p_4751_ = lean_ctor_get(v_m_4747_, 0);
        lean_inc_ref(v_p_4751_);
        v_m_4752_ = lean_ctor_get(v_m_4747_, 1);
        lean_inc(v_m_4752_);
        lean_dec_ref_known(v_m_4747_, 2);
        v_ofNat_4753_ = lean_ctor_get(v_inst_4745_, 3);
        v_npow_4754_ = lean_ctor_get(v_inst_4745_, 5);
        v_x_4755_ = lean_ctor_get(v_p_4751_, 0);
        lean_inc(v_x_4755_);
        v_k_4756_ = lean_ctor_get(v_p_4751_, 1);
        lean_inc(v_k_4756_);
        lean_dec_ref(v_p_4751_);
        v___x_4757_ = lean_unsigned_to_nat(0);
        v___x_4758_ = lean_nat_dec_eq(v_k_4756_, v___x_4757_);
        if v___x_4758_ == 0 {
            let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4760_: u8 = 0;
            v___x_4759_ = lean_unsigned_to_nat(1);
            v___x_4760_ = lean_nat_dec_eq(v_k_4756_, v___x_4759_);
            if v___x_4760_ == 0 {
                let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
                v___x_4761_ = l_Lean_RArray_getImpl___redArg(v_ctx_4746_, v_x_4755_);
                lean_dec(v_x_4755_);
                lean_inc(v_npow_4754_);
                v___x_4762_ = lean_apply_2(v_npow_4754_, v___x_4761_, v_k_4756_);
                v___x_4763_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4745_,
                    v_ctx_4746_,
                    v_m_4752_,
                    v___x_4762_,
                );
                return v___x_4763_;
            } else {
                let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_4756_);
                v___x_4764_ = l_Lean_RArray_getImpl___redArg(v_ctx_4746_, v_x_4755_);
                lean_dec(v_x_4755_);
                v___x_4765_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4745_,
                    v_ctx_4746_,
                    v_m_4752_,
                    v___x_4764_,
                );
                return v___x_4765_;
            }
        } else {
            let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_4756_);
            lean_dec(v_x_4755_);
            v___x_4766_ = lean_unsigned_to_nat(1);
            lean_inc(v_ofNat_4753_);
            v___x_4767_ = lean_apply_1(v_ofNat_4753_, v___x_4766_);
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
    mut v_inst_4769_: *mut LeanObject,
    mut v_ctx_4770_: *mut LeanObject,
    mut v_m_4771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4772_: *mut LeanObject = core::ptr::null_mut();
    v_res_4772_ =
        l_Lean_Grind_CommRing_Mon_denote_x27___redArg(v_inst_4769_, v_ctx_4770_, v_m_4771_);
    lean_dec_ref(v_ctx_4770_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denote_x27(
    mut v_00_u03b1_4773_: *mut LeanObject,
    mut v_inst_4774_: *mut LeanObject,
    mut v_ctx_4775_: *mut LeanObject,
    mut v_m_4776_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_4776_) == 0 {
        let mut v_ofNat_4777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
        v_ofNat_4777_ = lean_ctor_get(v_inst_4774_, 3);
        lean_inc(v_ofNat_4777_);
        lean_dec_ref(v_inst_4774_);
        v___x_4778_ = lean_unsigned_to_nat(1);
        v___x_4779_ = lean_apply_1(v_ofNat_4777_, v___x_4778_);
        return v___x_4779_;
    } else {
        let mut v_p_4780_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_4781_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_4782_: *mut LeanObject = core::ptr::null_mut();
        let mut v_npow_4783_: *mut LeanObject = core::ptr::null_mut();
        let mut v_x_4784_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4787_: u8 = 0;
        v_p_4780_ = lean_ctor_get(v_m_4776_, 0);
        lean_inc_ref(v_p_4780_);
        v_m_4781_ = lean_ctor_get(v_m_4776_, 1);
        lean_inc(v_m_4781_);
        lean_dec_ref_known(v_m_4776_, 2);
        v_ofNat_4782_ = lean_ctor_get(v_inst_4774_, 3);
        v_npow_4783_ = lean_ctor_get(v_inst_4774_, 5);
        v_x_4784_ = lean_ctor_get(v_p_4780_, 0);
        lean_inc(v_x_4784_);
        v_k_4785_ = lean_ctor_get(v_p_4780_, 1);
        lean_inc(v_k_4785_);
        lean_dec_ref(v_p_4780_);
        v___x_4786_ = lean_unsigned_to_nat(0);
        v___x_4787_ = lean_nat_dec_eq(v_k_4785_, v___x_4786_);
        if v___x_4787_ == 0 {
            let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4789_: u8 = 0;
            v___x_4788_ = lean_unsigned_to_nat(1);
            v___x_4789_ = lean_nat_dec_eq(v_k_4785_, v___x_4788_);
            if v___x_4789_ == 0 {
                let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
                v___x_4790_ = l_Lean_RArray_getImpl___redArg(v_ctx_4775_, v_x_4784_);
                lean_dec(v_x_4784_);
                lean_inc(v_npow_4783_);
                v___x_4791_ = lean_apply_2(v_npow_4783_, v___x_4790_, v_k_4785_);
                v___x_4792_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4774_,
                    v_ctx_4775_,
                    v_m_4781_,
                    v___x_4791_,
                );
                return v___x_4792_;
            } else {
                let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_4785_);
                v___x_4793_ = l_Lean_RArray_getImpl___redArg(v_ctx_4775_, v_x_4784_);
                lean_dec(v_x_4784_);
                v___x_4794_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_inst_4774_,
                    v_ctx_4775_,
                    v_m_4781_,
                    v___x_4793_,
                );
                return v___x_4794_;
            }
        } else {
            let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_4785_);
            lean_dec(v_x_4784_);
            v___x_4795_ = lean_unsigned_to_nat(1);
            lean_inc(v_ofNat_4782_);
            v___x_4796_ = lean_apply_1(v_ofNat_4782_, v___x_4795_);
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
    mut v_00_u03b1_4798_: *mut LeanObject,
    mut v_inst_4799_: *mut LeanObject,
    mut v_ctx_4800_: *mut LeanObject,
    mut v_m_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4802_: *mut LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lean_Grind_CommRing_Mon_denote_x27(
        v_00_u03b1_4798_,
        v_inst_4799_,
        v_ctx_4800_,
        v_m_4801_,
    );
    lean_dec_ref(v_ctx_4800_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_ofVar(mut v_x_4803_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    v___x_4804_ = lean_unsigned_to_nat(1);
    v___x_4805_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4805_, 0, v_x_4803_);
    lean_ctor_set(v___x_4805_, 1, v___x_4804_);
    v___x_4806_ = lean_box(0);
    v___x_4807_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4807_, 0, v___x_4805_);
    lean_ctor_set(v___x_4807_, 1, v___x_4806_);
    return v___x_4807_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_concat(
    mut v_m_u2081_4808_: *mut LeanObject,
    mut v_m_u2082_4809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4814_: u8 = 0;
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_u2081_4808_) == 0 {
                    lean_inc(v_m_u2082_4809_);
                    return v_m_u2082_4809_;
                } else {
                    v_p_4810_ = lean_ctor_get(v_m_u2081_4808_, 0);
                    v_m_4811_ = lean_ctor_get(v_m_u2081_4808_, 1);
                    v_isSharedCheck_4819_ = (!lean_is_exclusive(v_m_u2081_4808_)) as u8;
                    if v_isSharedCheck_4819_ == 0 {
                        v___x_4813_ = v_m_u2081_4808_;
                        v_isShared_4814_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_m_4811_);
                        lean_inc(v_p_4810_);
                        lean_dec(v_m_u2081_4808_);
                        v___x_4813_ = lean_box(0);
                        v_isShared_4814_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4815_ = l_Lean_Grind_CommRing_Mon_concat(v_m_4811_, v_m_u2082_4809_);
                if v_isShared_4814_ == 0 {
                    lean_ctor_set(v___x_4813_, 1, v___x_4815_);
                    v___x_4817_ = v___x_4813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_p_4810_);
                    lean_ctor_set(v_reuseFailAlloc_4818_, 1, v___x_4815_);
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
    mut v_m_u2081_4820_: *mut LeanObject,
    mut v_m_u2082_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4822_: *mut LeanObject = core::ptr::null_mut();
    v_res_4822_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_4820_, v_m_u2082_4821_);
    lean_dec(v_m_u2082_4821_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mulPow(
    mut v_pw_4823_: *mut LeanObject,
    mut v_m_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: u8 = 0;
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4831_: u8 = 0;
    let mut v___x_4832_: u8 = 0;
    let mut v_x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut v_unused_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4852_: u8 = 0;
    let mut v_unused_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_4824_) == 0 {
                    v___x_4825_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4825_, 0, v_pw_4823_);
                    lean_ctor_set(v___x_4825_, 1, v_m_4824_);
                    return v___x_4825_;
                } else {
                    v_p_4826_ = lean_ctor_get(v_m_4824_, 0);
                    lean_inc_ref(v_p_4826_);
                    v_m_4827_ = lean_ctor_get(v_m_4824_, 1);
                    v___x_4828_ = l_Lean_Grind_CommRing_Power_varLt(v_pw_4823_, v_p_4826_);
                    if v___x_4828_ == 0 {
                        lean_inc(v_m_4827_);
                        v_isSharedCheck_4852_ = (!lean_is_exclusive(v_m_4824_)) as u8;
                        if v_isSharedCheck_4852_ == 0 {
                            v_unused_4853_ = lean_ctor_get(v_m_4824_, 1);
                            lean_dec(v_unused_4853_);
                            v_unused_4854_ = lean_ctor_get(v_m_4824_, 0);
                            lean_dec(v_unused_4854_);
                            v___x_4830_ = v_m_4824_;
                            v_isShared_4831_ = v_isSharedCheck_4852_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_m_4824_);
                            v___x_4830_ = lean_box(0);
                            v_isShared_4831_ = v_isSharedCheck_4852_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_p_4826_);
                        v___x_4855_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4855_, 0, v_pw_4823_);
                        lean_ctor_set(v___x_4855_, 1, v_m_4824_);
                        return v___x_4855_;
                    }
                }
            }
            1 => {
                v___x_4832_ = l_Lean_Grind_CommRing_Power_varLt(v_p_4826_, v_pw_4823_);
                if v___x_4832_ == 0 {
                    v_x_4833_ = lean_ctor_get(v_pw_4823_, 0);
                    lean_inc(v_x_4833_);
                    v_k_4834_ = lean_ctor_get(v_pw_4823_, 1);
                    lean_inc(v_k_4834_);
                    lean_dec_ref(v_pw_4823_);
                    v_k_4835_ = lean_ctor_get(v_p_4826_, 1);
                    v_isSharedCheck_4846_ = (!lean_is_exclusive(v_p_4826_)) as u8;
                    if v_isSharedCheck_4846_ == 0 {
                        v_unused_4847_ = lean_ctor_get(v_p_4826_, 0);
                        lean_dec(v_unused_4847_);
                        v___x_4837_ = v_p_4826_;
                        v_isShared_4838_ = v_isSharedCheck_4846_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_4835_);
                        lean_dec(v_p_4826_);
                        v___x_4837_ = lean_box(0);
                        v_isShared_4838_ = v_isSharedCheck_4846_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4848_ = l_Lean_Grind_CommRing_Mon_mulPow(v_pw_4823_, v_m_4827_);
                    if v_isShared_4831_ == 0 {
                        lean_ctor_set(v___x_4830_, 1, v___x_4848_);
                        v___x_4850_ = v___x_4830_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_p_4826_);
                        lean_ctor_set(v_reuseFailAlloc_4851_, 1, v___x_4848_);
                        v___x_4850_ = v_reuseFailAlloc_4851_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4839_ = lean_nat_add(v_k_4834_, v_k_4835_);
                lean_dec(v_k_4835_);
                lean_dec(v_k_4834_);
                if v_isShared_4838_ == 0 {
                    lean_ctor_set(v___x_4837_, 1, v___x_4839_);
                    lean_ctor_set(v___x_4837_, 0, v_x_4833_);
                    v___x_4841_ = v___x_4837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_x_4833_);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 1, v___x_4839_);
                    v___x_4841_ = v_reuseFailAlloc_4845_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4831_ == 0 {
                    lean_ctor_set(v___x_4830_, 0, v___x_4841_);
                    v___x_4843_ = v___x_4830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4841_);
                    lean_ctor_set(v_reuseFailAlloc_4844_, 1, v_m_4827_);
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
    mut v_pw_4856_: *mut LeanObject,
    mut v_m_4857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4868_: u8 = 0;
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_unused_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_4857_) == 0 {
                    v___x_4858_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4858_, 0, v_pw_4856_);
                    lean_ctor_set(v___x_4858_, 1, v_m_4857_);
                    return v___x_4858_;
                } else {
                    v_p_4859_ = lean_ctor_get(v_m_4857_, 0);
                    lean_inc_ref(v_p_4859_);
                    v_m_4860_ = lean_ctor_get(v_m_4857_, 1);
                    v_x_4861_ = lean_ctor_get(v_pw_4856_, 0);
                    v_k_4862_ = lean_ctor_get(v_pw_4856_, 1);
                    v_x_4863_ = lean_ctor_get(v_p_4859_, 0);
                    v_k_4864_ = lean_ctor_get(v_p_4859_, 1);
                    v_isSharedCheck_4883_ = (!lean_is_exclusive(v_p_4859_)) as u8;
                    if v_isSharedCheck_4883_ == 0 {
                        v___x_4866_ = v_p_4859_;
                        v_isShared_4867_ = v_isSharedCheck_4883_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_4864_);
                        lean_inc(v_x_4863_);
                        lean_dec(v_p_4859_);
                        v___x_4866_ = lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4868_ = lean_nat_dec_eq(v_x_4861_, v_x_4863_);
                lean_dec(v_x_4863_);
                if v___x_4868_ == 0 {
                    lean_del_object(v___x_4866_);
                    lean_dec(v_k_4864_);
                    v___x_4869_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4869_, 0, v_pw_4856_);
                    lean_ctor_set(v___x_4869_, 1, v_m_4857_);
                    return v___x_4869_;
                } else {
                    lean_inc(v_k_4862_);
                    lean_inc(v_x_4861_);
                    lean_inc(v_m_4860_);
                    lean_dec_ref(v_pw_4856_);
                    v_isSharedCheck_4880_ = (!lean_is_exclusive(v_m_4857_)) as u8;
                    if v_isSharedCheck_4880_ == 0 {
                        v_unused_4881_ = lean_ctor_get(v_m_4857_, 1);
                        lean_dec(v_unused_4881_);
                        v_unused_4882_ = lean_ctor_get(v_m_4857_, 0);
                        lean_dec(v_unused_4882_);
                        v___x_4871_ = v_m_4857_;
                        v_isShared_4872_ = v_isSharedCheck_4880_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_4857_);
                        v___x_4871_ = lean_box(0);
                        v_isShared_4872_ = v_isSharedCheck_4880_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4873_ = lean_nat_add(v_k_4862_, v_k_4864_);
                lean_dec(v_k_4864_);
                lean_dec(v_k_4862_);
                if v_isShared_4867_ == 0 {
                    lean_ctor_set(v___x_4866_, 1, v___x_4873_);
                    lean_ctor_set(v___x_4866_, 0, v_x_4861_);
                    v___x_4875_ = v___x_4866_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_x_4861_);
                    lean_ctor_set(v_reuseFailAlloc_4879_, 1, v___x_4873_);
                    v___x_4875_ = v_reuseFailAlloc_4879_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4872_ == 0 {
                    lean_ctor_set(v___x_4871_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 1, v_m_4860_);
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
pub unsafe fn l_Lean_Grind_CommRing_Mon_length(mut v_x_4884_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_4884_) == 0 {
        let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
        v___x_4885_ = lean_unsigned_to_nat(0);
        return v___x_4885_;
    } else {
        let mut v_m_4886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
        v_m_4886_ = lean_ctor_get(v_x_4884_, 1);
        v___x_4887_ = lean_unsigned_to_nat(1);
        v___x_4888_ = l_Lean_Grind_CommRing_Mon_length(v_m_4886_);
        v___x_4889_ = lean_nat_add(v___x_4887_, v___x_4888_);
        lean_dec(v___x_4888_);
        return v___x_4889_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_length___boxed(
    mut v_x_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4891_: *mut LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_Lean_Grind_CommRing_Mon_length(v_x_4890_);
    lean_dec(v_x_4890_);
    return v_res_4891_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_hugeFuel() -> *mut LeanObject {
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    v___x_4892_ = lean_unsigned_to_nat(1000000);
    return v___x_4892_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul_go(
    mut v_fuel_4893_: *mut LeanObject,
    mut v_m_u2081_4894_: *mut LeanObject,
    mut v_m_u2082_4895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4897_: u8 = 0;
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: u8 = 0;
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4909_: u8 = 0;
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v_x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v_unused_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4929_: u8 = 0;
    let mut v_unused_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut v_unused_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_unused_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4896_ = lean_unsigned_to_nat(0);
                v_isZero_4897_ = lean_nat_dec_eq(v_fuel_4893_, v_zero_4896_);
                if v_isZero_4897_ == 1 {
                    v___x_4898_ =
                        l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_4894_, v_m_u2082_4895_);
                    lean_dec(v_m_u2082_4895_);
                    return v___x_4898_;
                } else {
                    if lean_obj_tag(v_m_u2082_4895_) == 0 {
                        return v_m_u2081_4894_;
                    } else {
                        if lean_obj_tag(v_m_u2081_4894_) == 0 {
                            return v_m_u2082_4895_;
                        } else {
                            v_p_4899_ = lean_ctor_get(v_m_u2082_4895_, 0);
                            lean_inc_ref(v_p_4899_);
                            v_m_4900_ = lean_ctor_get(v_m_u2082_4895_, 1);
                            v_p_4901_ = lean_ctor_get(v_m_u2081_4894_, 0);
                            v_m_4902_ = lean_ctor_get(v_m_u2081_4894_, 1);
                            v_one_4903_ = lean_unsigned_to_nat(1);
                            v_n_4904_ = lean_nat_sub(v_fuel_4893_, v_one_4903_);
                            v___x_4905_ = l_Lean_Grind_CommRing_Power_varLt(v_p_4901_, v_p_4899_);
                            if v___x_4905_ == 0 {
                                lean_inc(v_m_4900_);
                                v_isSharedCheck_4936_ = (!lean_is_exclusive(v_m_u2082_4895_)) as u8;
                                if v_isSharedCheck_4936_ == 0 {
                                    v_unused_4937_ = lean_ctor_get(v_m_u2082_4895_, 1);
                                    lean_dec(v_unused_4937_);
                                    v_unused_4938_ = lean_ctor_get(v_m_u2082_4895_, 0);
                                    lean_dec(v_unused_4938_);
                                    v___x_4907_ = v_m_u2082_4895_;
                                    v_isShared_4908_ = v_isSharedCheck_4936_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_m_u2082_4895_);
                                    v___x_4907_ = lean_box(0);
                                    v_isShared_4908_ = v_isSharedCheck_4936_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_inc(v_m_4902_);
                                lean_inc_ref(v_p_4901_);
                                lean_dec_ref(v_p_4899_);
                                v_isSharedCheck_4946_ = (!lean_is_exclusive(v_m_u2081_4894_)) as u8;
                                if v_isSharedCheck_4946_ == 0 {
                                    v_unused_4947_ = lean_ctor_get(v_m_u2081_4894_, 1);
                                    lean_dec(v_unused_4947_);
                                    v_unused_4948_ = lean_ctor_get(v_m_u2081_4894_, 0);
                                    lean_dec(v_unused_4948_);
                                    v___x_4940_ = v_m_u2081_4894_;
                                    v_isShared_4941_ = v_isSharedCheck_4946_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec(v_m_u2081_4894_);
                                    v___x_4940_ = lean_box(0);
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
                    lean_inc(v_m_4902_);
                    lean_inc_ref(v_p_4901_);
                    lean_del_object(v___x_4907_);
                    v_isSharedCheck_4929_ = (!lean_is_exclusive(v_m_u2081_4894_)) as u8;
                    if v_isSharedCheck_4929_ == 0 {
                        v_unused_4930_ = lean_ctor_get(v_m_u2081_4894_, 1);
                        lean_dec(v_unused_4930_);
                        v_unused_4931_ = lean_ctor_get(v_m_u2081_4894_, 0);
                        lean_dec(v_unused_4931_);
                        v___x_4911_ = v_m_u2081_4894_;
                        v_isShared_4912_ = v_isSharedCheck_4929_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_u2081_4894_);
                        v___x_4911_ = lean_box(0);
                        v_isShared_4912_ = v_isSharedCheck_4929_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4932_ =
                        l_Lean_Grind_CommRing_Mon_mul_go(v_n_4904_, v_m_u2081_4894_, v_m_4900_);
                    lean_dec(v_n_4904_);
                    if v_isShared_4908_ == 0 {
                        lean_ctor_set(v___x_4907_, 1, v___x_4932_);
                        v___x_4934_ = v___x_4907_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_p_4899_);
                        lean_ctor_set(v_reuseFailAlloc_4935_, 1, v___x_4932_);
                        v___x_4934_ = v_reuseFailAlloc_4935_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4913_ = lean_ctor_get(v_p_4901_, 0);
                lean_inc(v_x_4913_);
                v_k_4914_ = lean_ctor_get(v_p_4901_, 1);
                lean_inc(v_k_4914_);
                lean_dec_ref(v_p_4901_);
                v_k_4915_ = lean_ctor_get(v_p_4899_, 1);
                v_isSharedCheck_4927_ = (!lean_is_exclusive(v_p_4899_)) as u8;
                if v_isSharedCheck_4927_ == 0 {
                    v_unused_4928_ = lean_ctor_get(v_p_4899_, 0);
                    lean_dec(v_unused_4928_);
                    v___x_4917_ = v_p_4899_;
                    v_isShared_4918_ = v_isSharedCheck_4927_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_k_4915_);
                    lean_dec(v_p_4899_);
                    v___x_4917_ = lean_box(0);
                    v_isShared_4918_ = v_isSharedCheck_4927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4919_ = lean_nat_add(v_k_4914_, v_k_4915_);
                lean_dec(v_k_4915_);
                lean_dec(v_k_4914_);
                if v_isShared_4918_ == 0 {
                    lean_ctor_set(v___x_4917_, 1, v___x_4919_);
                    lean_ctor_set(v___x_4917_, 0, v_x_4913_);
                    v___x_4921_ = v___x_4917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_x_4913_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 1, v___x_4919_);
                    v___x_4921_ = v_reuseFailAlloc_4926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4922_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_4904_, v_m_4902_, v_m_4900_);
                lean_dec(v_n_4904_);
                if v_isShared_4912_ == 0 {
                    lean_ctor_set(v___x_4911_, 1, v___x_4922_);
                    lean_ctor_set(v___x_4911_, 0, v___x_4921_);
                    v___x_4924_ = v___x_4911_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4921_);
                    lean_ctor_set(v_reuseFailAlloc_4925_, 1, v___x_4922_);
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
                lean_dec(v_n_4904_);
                if v_isShared_4941_ == 0 {
                    lean_ctor_set(v___x_4940_, 1, v___x_4942_);
                    v___x_4944_ = v___x_4940_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_p_4901_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 1, v___x_4942_);
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
    mut v_fuel_4949_: *mut LeanObject,
    mut v_m_u2081_4950_: *mut LeanObject,
    mut v_m_u2082_4951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4952_: *mut LeanObject = core::ptr::null_mut();
    v_res_4952_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_4949_, v_m_u2081_4950_, v_m_u2082_4951_);
    lean_dec(v_fuel_4949_);
    return v_res_4952_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul(
    mut v_m_u2081_4953_: *mut LeanObject,
    mut v_m_u2082_4954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    v___x_4955_ = lean_unsigned_to_nat(1000000);
    v___x_4956_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_4955_, v_m_u2081_4953_, v_m_u2082_4954_);
    return v___x_4956_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(
    mut v_fuel_4957_: *mut LeanObject,
    mut v_h__1_4958_: *mut LeanObject,
    mut v_h__2_4959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4961_: u8 = 0;
    v_zero_4960_ = lean_unsigned_to_nat(0);
    v_isZero_4961_ = lean_nat_dec_eq(v_fuel_4957_, v_zero_4960_);
    if v_isZero_4961_ == 1 {
        let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4959_);
        v___x_4962_ = lean_box(0);
        v___x_4963_ = lean_apply_1(v_h__1_4958_, v___x_4962_);
        return v___x_4963_;
    } else {
        let mut v_one_4964_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_4965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4958_);
        v_one_4964_ = lean_unsigned_to_nat(1);
        v_n_4965_ = lean_nat_sub(v_fuel_4957_, v_one_4964_);
        v___x_4966_ = lean_apply_1(v_h__2_4959_, v_n_4965_);
        return v___x_4966_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(
    mut v_fuel_4967_: *mut LeanObject,
    mut v_h__1_4968_: *mut LeanObject,
    mut v_h__2_4969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4970_: *mut LeanObject = core::ptr::null_mut();
    v_res_4970_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_4967_, v_h__1_4968_, v_h__2_4969_);
    lean_dec(v_fuel_4967_);
    return v_res_4970_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(
    mut v_motive_4971_: *mut LeanObject,
    mut v_fuel_4972_: *mut LeanObject,
    mut v_h__1_4973_: *mut LeanObject,
    mut v_h__2_4974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4976_: u8 = 0;
    v_zero_4975_ = lean_unsigned_to_nat(0);
    v_isZero_4976_ = lean_nat_dec_eq(v_fuel_4972_, v_zero_4975_);
    if v_isZero_4976_ == 1 {
        let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4974_);
        v___x_4977_ = lean_box(0);
        v___x_4978_ = lean_apply_1(v_h__1_4973_, v___x_4977_);
        return v___x_4978_;
    } else {
        let mut v_one_4979_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_4980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4973_);
        v_one_4979_ = lean_unsigned_to_nat(1);
        v_n_4980_ = lean_nat_sub(v_fuel_4972_, v_one_4979_);
        v___x_4981_ = lean_apply_1(v_h__2_4974_, v_n_4980_);
        return v___x_4981_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(
    mut v_motive_4982_: *mut LeanObject,
    mut v_fuel_4983_: *mut LeanObject,
    mut v_h__1_4984_: *mut LeanObject,
    mut v_h__2_4985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4986_: *mut LeanObject = core::ptr::null_mut();
    v_res_4986_ =
        l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(
            v_motive_4982_,
            v_fuel_4983_,
            v_h__1_4984_,
            v_h__2_4985_,
        );
    lean_dec(v_fuel_4983_);
    return v_res_4986_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(
    mut v_m_u2081_4987_: *mut LeanObject,
    mut v_m_u2082_4988_: *mut LeanObject,
    mut v_h__1_4989_: *mut LeanObject,
    mut v_h__2_4990_: *mut LeanObject,
    mut v_h__3_4991_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2082_4988_) == 0 {
        let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4991_);
        lean_dec(v_h__2_4990_);
        v___x_4992_ = lean_apply_1(v_h__1_4989_, v_m_u2081_4987_);
        return v___x_4992_;
    } else {
        lean_dec(v_h__1_4989_);
        if lean_obj_tag(v_m_u2081_4987_) == 0 {
            let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4991_);
            v___x_4993_ = lean_apply_2(v_h__2_4990_, v_m_u2082_4988_, lean_box(0));
            return v___x_4993_;
        } else {
            let mut v_p_4994_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_4995_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_4996_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_4997_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_4990_);
            v_p_4994_ = lean_ctor_get(v_m_u2082_4988_, 0);
            lean_inc_ref(v_p_4994_);
            v_m_4995_ = lean_ctor_get(v_m_u2082_4988_, 1);
            lean_inc(v_m_4995_);
            lean_dec_ref_known(v_m_u2082_4988_, 2);
            v_p_4996_ = lean_ctor_get(v_m_u2081_4987_, 0);
            lean_inc_ref(v_p_4996_);
            v_m_4997_ = lean_ctor_get(v_m_u2081_4987_, 1);
            lean_inc(v_m_4997_);
            lean_dec_ref_known(v_m_u2081_4987_, 2);
            v___x_4998_ = lean_apply_4(v_h__3_4991_, v_p_4996_, v_m_4997_, v_p_4994_, v_m_4995_);
            return v___x_4998_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(
    mut v_motive_4999_: *mut LeanObject,
    mut v_m_u2081_5000_: *mut LeanObject,
    mut v_m_u2082_5001_: *mut LeanObject,
    mut v_h__1_5002_: *mut LeanObject,
    mut v_h__2_5003_: *mut LeanObject,
    mut v_h__3_5004_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2082_5001_) == 0 {
        let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_5004_);
        lean_dec(v_h__2_5003_);
        v___x_5005_ = lean_apply_1(v_h__1_5002_, v_m_u2081_5000_);
        return v___x_5005_;
    } else {
        lean_dec(v_h__1_5002_);
        if lean_obj_tag(v_m_u2081_5000_) == 0 {
            let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5004_);
            v___x_5006_ = lean_apply_2(v_h__2_5003_, v_m_u2082_5001_, lean_box(0));
            return v___x_5006_;
        } else {
            let mut v_p_5007_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5008_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5009_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5003_);
            v_p_5007_ = lean_ctor_get(v_m_u2082_5001_, 0);
            lean_inc_ref(v_p_5007_);
            v_m_5008_ = lean_ctor_get(v_m_u2082_5001_, 1);
            lean_inc(v_m_5008_);
            lean_dec_ref_known(v_m_u2082_5001_, 2);
            v_p_5009_ = lean_ctor_get(v_m_u2081_5000_, 0);
            lean_inc_ref(v_p_5009_);
            v_m_5010_ = lean_ctor_get(v_m_u2081_5000_, 1);
            lean_inc(v_m_5010_);
            lean_dec_ref_known(v_m_u2081_5000_, 2);
            v___x_5011_ = lean_apply_4(v_h__3_5004_, v_p_5009_, v_m_5010_, v_p_5007_, v_m_5008_);
            return v___x_5011_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_mul__nc(
    mut v_m_u2081_5012_: *mut LeanObject,
    mut v_m_u2082_5013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_m_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut v_unused_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_u2081_5012_) == 0 {
                    return v_m_u2082_5013_;
                } else {
                    v_m_5014_ = lean_ctor_get(v_m_u2081_5012_, 1);
                    if lean_obj_tag(v_m_5014_) == 0 {
                        v_p_5015_ = lean_ctor_get(v_m_u2081_5012_, 0);
                        lean_inc_ref(v_p_5015_);
                        lean_dec_ref_known(v_m_u2081_5012_, 2);
                        v___x_5016_ =
                            l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_5015_, v_m_u2082_5013_);
                        return v___x_5016_;
                    } else {
                        lean_inc(v_m_5014_);
                        v_p_5017_ = lean_ctor_get(v_m_u2081_5012_, 0);
                        v_isSharedCheck_5025_ = (!lean_is_exclusive(v_m_u2081_5012_)) as u8;
                        if v_isSharedCheck_5025_ == 0 {
                            v_unused_5026_ = lean_ctor_get(v_m_u2081_5012_, 1);
                            lean_dec(v_unused_5026_);
                            v___x_5019_ = v_m_u2081_5012_;
                            v_isShared_5020_ = v_isSharedCheck_5025_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_p_5017_);
                            lean_dec(v_m_u2081_5012_);
                            v___x_5019_ = lean_box(0);
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
                    lean_ctor_set(v___x_5019_, 1, v___x_5021_);
                    v___x_5023_ = v___x_5019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_p_5017_);
                    lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5021_);
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
pub unsafe fn l_Lean_Grind_CommRing_Mon_degree(mut v_x_5027_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_5027_) == 0 {
        let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
        v___x_5028_ = lean_unsigned_to_nat(0);
        return v___x_5028_;
    } else {
        let mut v_p_5029_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_5030_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5031_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
        v_p_5029_ = lean_ctor_get(v_x_5027_, 0);
        v_m_5030_ = lean_ctor_get(v_x_5027_, 1);
        v_k_5031_ = lean_ctor_get(v_p_5029_, 1);
        v___x_5032_ = l_Lean_Grind_CommRing_Mon_degree(v_m_5030_);
        v___x_5033_ = lean_nat_add(v_k_5031_, v___x_5032_);
        lean_dec(v___x_5032_);
        return v___x_5033_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degree___boxed(
    mut v_x_5034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5035_: *mut LeanObject = core::ptr::null_mut();
    v_res_5035_ = l_Lean_Grind_CommRing_Mon_degree(v_x_5034_);
    lean_dec(v_x_5034_);
    return v_res_5035_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(
    mut v_x_5036_: *mut LeanObject,
    mut v_h__1_5037_: *mut LeanObject,
    mut v_h__2_5038_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5036_) == 0 {
        let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5038_);
        v___x_5039_ = lean_box(0);
        v___x_5040_ = lean_apply_1(v_h__1_5037_, v___x_5039_);
        return v___x_5040_;
    } else {
        let mut v_p_5041_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_5042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5037_);
        v_p_5041_ = lean_ctor_get(v_x_5036_, 0);
        lean_inc_ref(v_p_5041_);
        v_m_5042_ = lean_ctor_get(v_x_5036_, 1);
        lean_inc(v_m_5042_);
        lean_dec_ref_known(v_x_5036_, 2);
        v___x_5043_ = lean_apply_2(v_h__2_5038_, v_p_5041_, v_m_5042_);
        return v___x_5043_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(
    mut v_motive_5044_: *mut LeanObject,
    mut v_x_5045_: *mut LeanObject,
    mut v_h__1_5046_: *mut LeanObject,
    mut v_h__2_5047_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5045_) == 0 {
        let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5047_);
        v___x_5048_ = lean_box(0);
        v___x_5049_ = lean_apply_1(v_h__1_5046_, v___x_5048_);
        return v___x_5049_;
    } else {
        let mut v_p_5050_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_5051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5046_);
        v_p_5050_ = lean_ctor_get(v_x_5045_, 0);
        lean_inc_ref(v_p_5050_);
        v_m_5051_ = lean_ctor_get(v_x_5045_, 1);
        lean_inc(v_m_5051_);
        lean_dec_ref_known(v_x_5045_, 2);
        v___x_5052_ = lean_apply_2(v_h__2_5047_, v_p_5050_, v_m_5051_);
        return v___x_5052_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Var_revlex(
    mut v_x_5053_: *mut LeanObject,
    mut v_y_5054_: *mut LeanObject,
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
    mut v_x_5060_: *mut LeanObject,
    mut v_y_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5062_: u8 = 0;
    let mut v_r_5063_: *mut LeanObject = core::ptr::null_mut();
    v_res_5062_ = l_Lean_Grind_CommRing_Var_revlex(v_x_5060_, v_y_5061_);
    lean_dec(v_y_5061_);
    lean_dec(v_x_5060_);
    v_r_5063_ = lean_box((v_res_5062_) as usize);
    return v_r_5063_;
}
pub unsafe fn l_Lean_Grind_CommRing_powerRevlex(
    mut v_k_u2081_5064_: *mut LeanObject,
    mut v_k_u2082_5065_: *mut LeanObject,
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
    mut v_k_u2081_5071_: *mut LeanObject,
    mut v_k_u2082_5072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5073_: u8 = 0;
    let mut v_r_5074_: *mut LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_5071_, v_k_u2082_5072_);
    lean_dec(v_k_u2082_5072_);
    lean_dec(v_k_u2081_5071_);
    v_r_5074_ = lean_box((v_res_5073_) as usize);
    return v_r_5074_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(
    mut v_c_5075_: u8,
    mut v_h__1_5076_: *mut LeanObject,
    mut v_h__2_5077_: *mut LeanObject,
) -> *mut LeanObject {
    if v_c_5075_ == 0 {
        let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5076_);
        v___x_5078_ = lean_box(0);
        v___x_5079_ = lean_apply_1(v_h__2_5077_, v___x_5078_);
        return v___x_5079_;
    } else {
        let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5077_);
        v___x_5080_ = lean_box(0);
        v___x_5081_ = lean_apply_1(v_h__1_5076_, v___x_5080_);
        return v___x_5081_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(
    mut v_c_5082_: *mut LeanObject,
    mut v_h__1_5083_: *mut LeanObject,
    mut v_h__2_5084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_26__boxed_5085_: u8 = 0;
    let mut v_res_5086_: *mut LeanObject = core::ptr::null_mut();
    v_c_26__boxed_5085_ = (lean_unbox(v_c_5082_) as u8);
    v_res_5086_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(
        v_c_26__boxed_5085_,
        v_h__1_5083_,
        v_h__2_5084_,
    );
    return v_res_5086_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(
    mut v_motive_5087_: *mut LeanObject,
    mut v_c_5088_: u8,
    mut v_h__1_5089_: *mut LeanObject,
    mut v_h__2_5090_: *mut LeanObject,
) -> *mut LeanObject {
    if v_c_5088_ == 0 {
        let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5089_);
        v___x_5091_ = lean_box(0);
        v___x_5092_ = lean_apply_1(v_h__2_5090_, v___x_5091_);
        return v___x_5092_;
    } else {
        let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5090_);
        v___x_5093_ = lean_box(0);
        v___x_5094_ = lean_apply_1(v_h__1_5089_, v___x_5093_);
        return v___x_5094_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(
    mut v_motive_5095_: *mut LeanObject,
    mut v_c_5096_: *mut LeanObject,
    mut v_h__1_5097_: *mut LeanObject,
    mut v_h__2_5098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_37__boxed_5099_: u8 = 0;
    let mut v_res_5100_: *mut LeanObject = core::ptr::null_mut();
    v_c_37__boxed_5099_ = (lean_unbox(v_c_5096_) as u8);
    v_res_5100_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(
        v_motive_5095_,
        v_c_37__boxed_5099_,
        v_h__1_5097_,
        v_h__2_5098_,
    );
    return v_res_5100_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_revlex(
    mut v_p_u2081_5101_: *mut LeanObject,
    mut v_p_u2082_5102_: *mut LeanObject,
) -> u8 {
    let mut v_x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    v_x_5103_ = lean_ctor_get(v_p_u2081_5101_, 0);
    v_k_5104_ = lean_ctor_get(v_p_u2081_5101_, 1);
    v_x_5105_ = lean_ctor_get(v_p_u2082_5102_, 0);
    v_k_5106_ = lean_ctor_get(v_p_u2082_5102_, 1);
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
    mut v_p_u2081_5109_: *mut LeanObject,
    mut v_p_u2082_5110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5111_: u8 = 0;
    let mut v_r_5112_: *mut LeanObject = core::ptr::null_mut();
    v_res_5111_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_5109_, v_p_u2082_5110_);
    lean_dec_ref(v_p_u2082_5110_);
    lean_dec_ref(v_p_u2081_5109_);
    v_r_5112_ = lean_box((v_res_5111_) as usize);
    return v_r_5112_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlexWF(
    mut v_m_u2081_5113_: *mut LeanObject,
    mut v_m_u2082_5114_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_m_u2081_5113_) == 0 {
        if lean_obj_tag(v_m_u2082_5114_) == 0 {
            let mut v___x_5115_: u8 = 0;
            v___x_5115_ = 1;
            return v___x_5115_;
        } else {
            let mut v___x_5116_: u8 = 0;
            v___x_5116_ = 2;
            return v___x_5116_;
        }
    } else {
        if lean_obj_tag(v_m_u2082_5114_) == 0 {
            let mut v___x_5117_: u8 = 0;
            v___x_5117_ = 0;
            return v___x_5117_;
        } else {
            let mut v_p_5118_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5119_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5120_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5121_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5122_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5123_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5124_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5125_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5126_: u8 = 0;
            v_p_5118_ = lean_ctor_get(v_m_u2081_5113_, 0);
            v_p_5119_ = lean_ctor_get(v_m_u2082_5114_, 0);
            v_m_5120_ = lean_ctor_get(v_m_u2081_5113_, 1);
            v_m_5121_ = lean_ctor_get(v_m_u2082_5114_, 1);
            v_x_5122_ = lean_ctor_get(v_p_5118_, 0);
            v_k_5123_ = lean_ctor_get(v_p_5118_, 1);
            v_x_5124_ = lean_ctor_get(v_p_5119_, 0);
            v_k_5125_ = lean_ctor_get(v_p_5119_, 1);
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
    mut v_m_u2081_5134_: *mut LeanObject,
    mut v_m_u2082_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5136_: u8 = 0;
    let mut v_r_5137_: *mut LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_5134_, v_m_u2082_5135_);
    lean_dec(v_m_u2082_5135_);
    lean_dec(v_m_u2081_5134_);
    v_r_5137_ = lean_box((v_res_5136_) as usize);
    return v_r_5137_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(
    mut v_m_u2081_5138_: *mut LeanObject,
    mut v_m_u2082_5139_: *mut LeanObject,
    mut v_h__1_5140_: *mut LeanObject,
    mut v_h__2_5141_: *mut LeanObject,
    mut v_h__3_5142_: *mut LeanObject,
    mut v_h__4_5143_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2081_5138_) == 0 {
        lean_dec(v_h__4_5143_);
        lean_dec(v_h__3_5142_);
        if lean_obj_tag(v_m_u2082_5139_) == 0 {
            let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5141_);
            v___x_5144_ = lean_box(0);
            v___x_5145_ = lean_apply_1(v_h__1_5140_, v___x_5144_);
            return v___x_5145_;
        } else {
            let mut v_p_5146_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5147_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_5140_);
            v_p_5146_ = lean_ctor_get(v_m_u2082_5139_, 0);
            lean_inc_ref(v_p_5146_);
            v_m_5147_ = lean_ctor_get(v_m_u2082_5139_, 1);
            lean_inc(v_m_5147_);
            lean_dec_ref_known(v_m_u2082_5139_, 2);
            v___x_5148_ = lean_apply_2(v_h__2_5141_, v_p_5146_, v_m_5147_);
            return v___x_5148_;
        }
    } else {
        lean_dec(v_h__2_5141_);
        lean_dec(v_h__1_5140_);
        if lean_obj_tag(v_m_u2082_5139_) == 0 {
            let mut v_p_5149_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_5143_);
            v_p_5149_ = lean_ctor_get(v_m_u2081_5138_, 0);
            lean_inc_ref(v_p_5149_);
            v_m_5150_ = lean_ctor_get(v_m_u2081_5138_, 1);
            lean_inc(v_m_5150_);
            lean_dec_ref_known(v_m_u2081_5138_, 2);
            v___x_5151_ = lean_apply_2(v_h__3_5142_, v_p_5149_, v_m_5150_);
            return v___x_5151_;
        } else {
            let mut v_p_5152_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5153_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5154_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5155_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5142_);
            v_p_5152_ = lean_ctor_get(v_m_u2081_5138_, 0);
            lean_inc_ref(v_p_5152_);
            v_m_5153_ = lean_ctor_get(v_m_u2081_5138_, 1);
            lean_inc(v_m_5153_);
            lean_dec_ref_known(v_m_u2081_5138_, 2);
            v_p_5154_ = lean_ctor_get(v_m_u2082_5139_, 0);
            lean_inc_ref(v_p_5154_);
            v_m_5155_ = lean_ctor_get(v_m_u2082_5139_, 1);
            lean_inc(v_m_5155_);
            lean_dec_ref_known(v_m_u2082_5139_, 2);
            v___x_5156_ = lean_apply_4(v_h__4_5143_, v_p_5152_, v_m_5153_, v_p_5154_, v_m_5155_);
            return v___x_5156_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(
    mut v_motive_5157_: *mut LeanObject,
    mut v_m_u2081_5158_: *mut LeanObject,
    mut v_m_u2082_5159_: *mut LeanObject,
    mut v_h__1_5160_: *mut LeanObject,
    mut v_h__2_5161_: *mut LeanObject,
    mut v_h__3_5162_: *mut LeanObject,
    mut v_h__4_5163_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2081_5158_) == 0 {
        lean_dec(v_h__4_5163_);
        lean_dec(v_h__3_5162_);
        if lean_obj_tag(v_m_u2082_5159_) == 0 {
            let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5161_);
            v___x_5164_ = lean_box(0);
            v___x_5165_ = lean_apply_1(v_h__1_5160_, v___x_5164_);
            return v___x_5165_;
        } else {
            let mut v_p_5166_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5167_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_5160_);
            v_p_5166_ = lean_ctor_get(v_m_u2082_5159_, 0);
            lean_inc_ref(v_p_5166_);
            v_m_5167_ = lean_ctor_get(v_m_u2082_5159_, 1);
            lean_inc(v_m_5167_);
            lean_dec_ref_known(v_m_u2082_5159_, 2);
            v___x_5168_ = lean_apply_2(v_h__2_5161_, v_p_5166_, v_m_5167_);
            return v___x_5168_;
        }
    } else {
        lean_dec(v_h__2_5161_);
        lean_dec(v_h__1_5160_);
        if lean_obj_tag(v_m_u2082_5159_) == 0 {
            let mut v_p_5169_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5170_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_5163_);
            v_p_5169_ = lean_ctor_get(v_m_u2081_5158_, 0);
            lean_inc_ref(v_p_5169_);
            v_m_5170_ = lean_ctor_get(v_m_u2081_5158_, 1);
            lean_inc(v_m_5170_);
            lean_dec_ref_known(v_m_u2081_5158_, 2);
            v___x_5171_ = lean_apply_2(v_h__3_5162_, v_p_5169_, v_m_5170_);
            return v___x_5171_;
        } else {
            let mut v_p_5172_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5173_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5174_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5162_);
            v_p_5172_ = lean_ctor_get(v_m_u2081_5158_, 0);
            lean_inc_ref(v_p_5172_);
            v_m_5173_ = lean_ctor_get(v_m_u2081_5158_, 1);
            lean_inc(v_m_5173_);
            lean_dec_ref_known(v_m_u2081_5158_, 2);
            v_p_5174_ = lean_ctor_get(v_m_u2082_5159_, 0);
            lean_inc_ref(v_p_5174_);
            v_m_5175_ = lean_ctor_get(v_m_u2082_5159_, 1);
            lean_inc(v_m_5175_);
            lean_dec_ref_known(v_m_u2082_5159_, 2);
            v___x_5176_ = lean_apply_4(v_h__4_5163_, v_p_5172_, v_m_5173_, v_p_5174_, v_m_5175_);
            return v___x_5176_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlexFuel(
    mut v_fuel_5177_: *mut LeanObject,
    mut v_m_u2081_5178_: *mut LeanObject,
    mut v_m_u2082_5179_: *mut LeanObject,
) -> u8 {
    let mut v_zero_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5181_: u8 = 0;
    v_zero_5180_ = lean_unsigned_to_nat(0);
    v_isZero_5181_ = lean_nat_dec_eq(v_fuel_5177_, v_zero_5180_);
    if v_isZero_5181_ == 1 {
        let mut v___x_5182_: u8 = 0;
        v___x_5182_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_5178_, v_m_u2082_5179_);
        return v___x_5182_;
    } else {
        if lean_obj_tag(v_m_u2081_5178_) == 0 {
            if lean_obj_tag(v_m_u2082_5179_) == 0 {
                let mut v___x_5183_: u8 = 0;
                v___x_5183_ = 1;
                return v___x_5183_;
            } else {
                let mut v___x_5184_: u8 = 0;
                v___x_5184_ = 2;
                return v___x_5184_;
            }
        } else {
            if lean_obj_tag(v_m_u2082_5179_) == 0 {
                let mut v___x_5185_: u8 = 0;
                v___x_5185_ = 0;
                return v___x_5185_;
            } else {
                let mut v_p_5186_: *mut LeanObject = core::ptr::null_mut();
                let mut v_p_5187_: *mut LeanObject = core::ptr::null_mut();
                let mut v_m_5188_: *mut LeanObject = core::ptr::null_mut();
                let mut v_m_5189_: *mut LeanObject = core::ptr::null_mut();
                let mut v_x_5190_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_5191_: *mut LeanObject = core::ptr::null_mut();
                let mut v_x_5192_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_5193_: *mut LeanObject = core::ptr::null_mut();
                let mut v_one_5194_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_5195_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5196_: u8 = 0;
                v_p_5186_ = lean_ctor_get(v_m_u2081_5178_, 0);
                v_p_5187_ = lean_ctor_get(v_m_u2082_5179_, 0);
                v_m_5188_ = lean_ctor_get(v_m_u2081_5178_, 1);
                v_m_5189_ = lean_ctor_get(v_m_u2082_5179_, 1);
                v_x_5190_ = lean_ctor_get(v_p_5186_, 0);
                v_k_5191_ = lean_ctor_get(v_p_5186_, 1);
                v_x_5192_ = lean_ctor_get(v_p_5187_, 0);
                v_k_5193_ = lean_ctor_get(v_p_5187_, 1);
                v_one_5194_ = lean_unsigned_to_nat(1);
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
                        lean_dec(v_n_5195_);
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
                        lean_dec(v_n_5195_);
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
                    lean_dec(v_n_5195_);
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
    mut v_fuel_5204_: *mut LeanObject,
    mut v_m_u2081_5205_: *mut LeanObject,
    mut v_m_u2082_5206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5207_: u8 = 0;
    let mut v_r_5208_: *mut LeanObject = core::ptr::null_mut();
    v_res_5207_ =
        l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_5204_, v_m_u2081_5205_, v_m_u2082_5206_);
    lean_dec(v_m_u2082_5206_);
    lean_dec(v_m_u2081_5205_);
    lean_dec(v_fuel_5204_);
    v_r_5208_ = lean_box((v_res_5207_) as usize);
    return v_r_5208_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlex(
    mut v_m_u2081_5209_: *mut LeanObject,
    mut v_m_u2082_5210_: *mut LeanObject,
) -> u8 {
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: u8 = 0;
    v___x_5211_ = lean_unsigned_to_nat(1000000);
    v___x_5212_ =
        l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_5211_, v_m_u2081_5209_, v_m_u2082_5210_);
    return v___x_5212_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_revlex___boxed(
    mut v_m_u2081_5213_: *mut LeanObject,
    mut v_m_u2082_5214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5215_: u8 = 0;
    let mut v_r_5216_: *mut LeanObject = core::ptr::null_mut();
    v_res_5215_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_5213_, v_m_u2082_5214_);
    lean_dec(v_m_u2082_5214_);
    lean_dec(v_m_u2081_5213_);
    v_r_5216_ = lean_box((v_res_5215_) as usize);
    return v_r_5216_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_grevlex(
    mut v_m_u2081_5217_: *mut LeanObject,
    mut v_m_u2082_5218_: *mut LeanObject,
) -> u8 {
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: u8 = 0;
    v___x_5219_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_5217_);
    v___x_5220_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_5218_);
    v___x_5221_ = lean_nat_dec_lt(v___x_5219_, v___x_5220_);
    if v___x_5221_ == 0 {
        let mut v___x_5222_: u8 = 0;
        v___x_5222_ = lean_nat_dec_eq(v___x_5219_, v___x_5220_);
        lean_dec(v___x_5220_);
        lean_dec(v___x_5219_);
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
        lean_dec(v___x_5220_);
        lean_dec(v___x_5219_);
        v___x_5225_ = 0;
        return v___x_5225_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_grevlex___boxed(
    mut v_m_u2081_5226_: *mut LeanObject,
    mut v_m_u2082_5227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5228_: u8 = 0;
    let mut v_r_5229_: *mut LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_5226_, v_m_u2082_5227_);
    lean_dec(v_m_u2082_5227_);
    lean_dec(v_m_u2081_5226_);
    v_r_5229_ = lean_box((v_res_5228_) as usize);
    return v_r_5229_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorIdx(
    mut v_x_5230_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5230_) == 0 {
        let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
        v___x_5231_ = lean_unsigned_to_nat(0);
        return v___x_5231_;
    } else {
        let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
        v___x_5232_ = lean_unsigned_to_nat(1);
        return v___x_5232_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(
    mut v_x_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5234_: *mut LeanObject = core::ptr::null_mut();
    v_res_5234_ = l_Lean_Grind_CommRing_Poly_ctorIdx(v_x_5233_);
    lean_dec_ref(v_x_5233_);
    return v_res_5234_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorElim___redArg(
    mut v_t_5235_: *mut LeanObject,
    mut v_k_5236_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5235_) == 0 {
        let mut v_k_5237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
        v_k_5237_ = lean_ctor_get(v_t_5235_, 0);
        lean_inc(v_k_5237_);
        lean_dec_ref_known(v_t_5235_, 1);
        v___x_5238_ = lean_apply_1(v_k_5236_, v_k_5237_);
        return v___x_5238_;
    } else {
        let mut v_k_5239_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5240_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
        v_k_5239_ = lean_ctor_get(v_t_5235_, 0);
        lean_inc(v_k_5239_);
        v_v_5240_ = lean_ctor_get(v_t_5235_, 1);
        lean_inc(v_v_5240_);
        v_p_5241_ = lean_ctor_get(v_t_5235_, 2);
        lean_inc_ref(v_p_5241_);
        lean_dec_ref_known(v_t_5235_, 3);
        v___x_5242_ = lean_apply_3(v_k_5236_, v_k_5239_, v_v_5240_, v_p_5241_);
        return v___x_5242_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorElim(
    mut v_motive_5243_: *mut LeanObject,
    mut v_ctorIdx_5244_: *mut LeanObject,
    mut v_t_5245_: *mut LeanObject,
    mut v_h_5246_: *mut LeanObject,
    mut v_k_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    v___x_5248_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5245_, v_k_5247_);
    return v___x_5248_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ctorElim___boxed(
    mut v_motive_5249_: *mut LeanObject,
    mut v_ctorIdx_5250_: *mut LeanObject,
    mut v_t_5251_: *mut LeanObject,
    mut v_h_5252_: *mut LeanObject,
    mut v_k_5253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5254_: *mut LeanObject = core::ptr::null_mut();
    v_res_5254_ = l_Lean_Grind_CommRing_Poly_ctorElim(
        v_motive_5249_,
        v_ctorIdx_5250_,
        v_t_5251_,
        v_h_5252_,
        v_k_5253_,
    );
    lean_dec(v_ctorIdx_5250_);
    return v_res_5254_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_num_elim___redArg(
    mut v_t_5255_: *mut LeanObject,
    mut v_num_5256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5255_, v_num_5256_);
    return v___x_5257_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_num_elim(
    mut v_motive_5258_: *mut LeanObject,
    mut v_t_5259_: *mut LeanObject,
    mut v_h_5260_: *mut LeanObject,
    mut v_num_5261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    v___x_5262_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5259_, v_num_5261_);
    return v___x_5262_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_add_elim___redArg(
    mut v_t_5263_: *mut LeanObject,
    mut v_add_5264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    v___x_5265_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5263_, v_add_5264_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_add_elim(
    mut v_motive_5266_: *mut LeanObject,
    mut v_t_5267_: *mut LeanObject,
    mut v_h_5268_: *mut LeanObject,
    mut v_add_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    v___x_5270_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_5267_, v_add_5269_);
    return v___x_5270_;
}
pub unsafe fn l_Lean_Grind_CommRing_instBEqPoly_beq(
    mut v_x_5271_: *mut LeanObject,
    mut v_x_5272_: *mut LeanObject,
) -> u8 {
    let mut v_k_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: u8 = 0;
    let mut v___x_5276_: u8 = 0;
    let mut v_k_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5271_) == 0 {
                    if lean_obj_tag(v_x_5272_) == 0 {
                        v_k_5273_ = lean_ctor_get(v_x_5271_, 0);
                        v_k_5274_ = lean_ctor_get(v_x_5272_, 0);
                        v___x_5275_ = lean_int_dec_eq(v_k_5273_, v_k_5274_);
                        return v___x_5275_;
                    } else {
                        v___x_5276_ = 0;
                        return v___x_5276_;
                    }
                } else {
                    if lean_obj_tag(v_x_5272_) == 1 {
                        v_k_5277_ = lean_ctor_get(v_x_5271_, 0);
                        v_v_5278_ = lean_ctor_get(v_x_5271_, 1);
                        v_p_5279_ = lean_ctor_get(v_x_5271_, 2);
                        v_k_5280_ = lean_ctor_get(v_x_5272_, 0);
                        v_v_5281_ = lean_ctor_get(v_x_5272_, 1);
                        v_p_5282_ = lean_ctor_get(v_x_5272_, 2);
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
    mut v_x_5287_: *mut LeanObject,
    mut v_x_5288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5289_: u8 = 0;
    let mut v_r_5290_: *mut LeanObject = core::ptr::null_mut();
    v_res_5289_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_5287_, v_x_5288_);
    lean_dec_ref(v_x_5288_);
    lean_dec_ref(v_x_5287_);
    v_r_5290_ = lean_box((v_res_5289_) as usize);
    return v_r_5290_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(
    mut v_x_5293_: *mut LeanObject,
    mut v_x_5294_: *mut LeanObject,
    mut v_h__1_5295_: *mut LeanObject,
    mut v_h__2_5296_: *mut LeanObject,
    mut v_h__3_5297_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5293_) == 0 {
        lean_dec(v_h__2_5296_);
        if lean_obj_tag(v_x_5294_) == 0 {
            let mut v_k_5298_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5299_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5297_);
            v_k_5298_ = lean_ctor_get(v_x_5293_, 0);
            lean_inc(v_k_5298_);
            lean_dec_ref_known(v_x_5293_, 1);
            v_k_5299_ = lean_ctor_get(v_x_5294_, 0);
            lean_inc(v_k_5299_);
            lean_dec_ref_known(v_x_5294_, 1);
            v___x_5300_ = lean_apply_2(v_h__1_5295_, v_k_5298_, v_k_5299_);
            return v___x_5300_;
        } else {
            let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_5295_);
            v___x_5301_ =
                lean_apply_4(v_h__3_5297_, v_x_5293_, v_x_5294_, lean_box(0), lean_box(0));
            return v___x_5301_;
        }
    } else {
        lean_dec(v_h__1_5295_);
        if lean_obj_tag(v_x_5294_) == 1 {
            let mut v_k_5302_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_5303_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5304_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5305_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_5306_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5307_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5297_);
            v_k_5302_ = lean_ctor_get(v_x_5293_, 0);
            lean_inc(v_k_5302_);
            v_v_5303_ = lean_ctor_get(v_x_5293_, 1);
            lean_inc(v_v_5303_);
            v_p_5304_ = lean_ctor_get(v_x_5293_, 2);
            lean_inc_ref(v_p_5304_);
            lean_dec_ref_known(v_x_5293_, 3);
            v_k_5305_ = lean_ctor_get(v_x_5294_, 0);
            lean_inc(v_k_5305_);
            v_v_5306_ = lean_ctor_get(v_x_5294_, 1);
            lean_inc(v_v_5306_);
            v_p_5307_ = lean_ctor_get(v_x_5294_, 2);
            lean_inc_ref(v_p_5307_);
            lean_dec_ref_known(v_x_5294_, 3);
            v___x_5308_ = lean_apply_6(
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
            let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5296_);
            v___x_5309_ =
                lean_apply_4(v_h__3_5297_, v_x_5293_, v_x_5294_, lean_box(0), lean_box(0));
            return v___x_5309_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(
    mut v_motive_5310_: *mut LeanObject,
    mut v_x_5311_: *mut LeanObject,
    mut v_x_5312_: *mut LeanObject,
    mut v_h__1_5313_: *mut LeanObject,
    mut v_h__2_5314_: *mut LeanObject,
    mut v_h__3_5315_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5311_) == 0 {
        lean_dec(v_h__2_5314_);
        if lean_obj_tag(v_x_5312_) == 0 {
            let mut v_k_5316_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5315_);
            v_k_5316_ = lean_ctor_get(v_x_5311_, 0);
            lean_inc(v_k_5316_);
            lean_dec_ref_known(v_x_5311_, 1);
            v_k_5317_ = lean_ctor_get(v_x_5312_, 0);
            lean_inc(v_k_5317_);
            lean_dec_ref_known(v_x_5312_, 1);
            v___x_5318_ = lean_apply_2(v_h__1_5313_, v_k_5316_, v_k_5317_);
            return v___x_5318_;
        } else {
            let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_5313_);
            v___x_5319_ =
                lean_apply_4(v_h__3_5315_, v_x_5311_, v_x_5312_, lean_box(0), lean_box(0));
            return v___x_5319_;
        }
    } else {
        lean_dec(v_h__1_5313_);
        if lean_obj_tag(v_x_5312_) == 1 {
            let mut v_k_5320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_5321_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5322_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5323_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_5324_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_5325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5315_);
            v_k_5320_ = lean_ctor_get(v_x_5311_, 0);
            lean_inc(v_k_5320_);
            v_v_5321_ = lean_ctor_get(v_x_5311_, 1);
            lean_inc(v_v_5321_);
            v_p_5322_ = lean_ctor_get(v_x_5311_, 2);
            lean_inc_ref(v_p_5322_);
            lean_dec_ref_known(v_x_5311_, 3);
            v_k_5323_ = lean_ctor_get(v_x_5312_, 0);
            lean_inc(v_k_5323_);
            v_v_5324_ = lean_ctor_get(v_x_5312_, 1);
            lean_inc(v_v_5324_);
            v_p_5325_ = lean_ctor_get(v_x_5312_, 2);
            lean_inc_ref(v_p_5325_);
            lean_dec_ref_known(v_x_5312_, 3);
            v___x_5326_ = lean_apply_6(
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
            let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5314_);
            v___x_5327_ =
                lean_apply_4(v_h__3_5315_, v_x_5311_, v_x_5312_, lean_box(0), lean_box(0));
            return v___x_5327_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_instReprPoly_repr(
    mut v_x_5340_: *mut LeanObject,
    mut v_prec_5341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: u8 = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___y_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: u8 = 0;
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_k_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: u8 = 0;
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: u8 = 0;
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5340_) == 0 {
                    v_k_5351_ = lean_ctor_get(v_x_5340_, 0);
                    v_isSharedCheck_5374_ = (!lean_is_exclusive(v_x_5340_)) as u8;
                    if v_isSharedCheck_5374_ == 0 {
                        v___x_5353_ = v_x_5340_;
                        v_isShared_5354_ = v_isSharedCheck_5374_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_5351_);
                        lean_dec(v_x_5340_);
                        v___x_5353_ = lean_box(0);
                        v_isShared_5354_ = v_isSharedCheck_5374_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_5375_ = lean_ctor_get(v_x_5340_, 0);
                    lean_inc(v_k_5375_);
                    v_v_5376_ = lean_ctor_get(v_x_5340_, 1);
                    lean_inc(v_v_5376_);
                    v_p_5377_ = lean_ctor_get(v_x_5340_, 2);
                    lean_inc_ref(v_p_5377_);
                    lean_dec_ref_known(v_x_5340_, 3);
                    v___x_5378_ = lean_unsigned_to_nat(1024);
                    v___x_5406_ = lean_nat_dec_le(v___x_5378_, v_prec_5341_);
                    if v___x_5406_ == 0 {
                        v___x_5407_ = lean_obj_once(
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
                        v___x_5408_ = lean_obj_once(
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
                lean_inc(v___y_5343_);
                v___x_5346_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5346_, 0, v___y_5343_);
                lean_ctor_set(v___x_5346_, 1, v___y_5345_);
                lean_inc(v___y_5344_);
                v___x_5347_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5347_, 0, v___y_5344_);
                lean_ctor_set(v___x_5347_, 1, v___x_5346_);
                v___x_5348_ = 0;
                v___x_5349_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5349_, 0, v___x_5347_);
                lean_ctor_set_uint8(
                    v___x_5349_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5348_,
                );
                v___x_5350_ = l_Repr_addAppParen(v___x_5349_, v_prec_5341_);
                return v___x_5350_;
            }
            2 => {
                v___x_5370_ = lean_unsigned_to_nat(1024);
                v___x_5371_ = lean_nat_dec_le(v___x_5370_, v_prec_5341_);
                if v___x_5371_ == 0 {
                    v___x_5372_ = lean_obj_once(
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
                    v___x_5373_ = lean_obj_once(
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
                v___x_5358_ = lean_obj_once(
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
                    lean_dec(v_k_5351_);
                    if v_isShared_5354_ == 0 {
                        lean_ctor_set_tag(v___x_5353_, 3);
                        lean_ctor_set(v___x_5353_, 0, v___x_5360_);
                        v___x_5362_ = v___x_5353_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5363_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5360_);
                        v___x_5362_ = v_reuseFailAlloc_5363_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_5364_ = lean_unsigned_to_nat(1024);
                    v___x_5365_ = l_Int_repr(v_k_5351_);
                    lean_dec(v_k_5351_);
                    if v_isShared_5354_ == 0 {
                        lean_ctor_set_tag(v___x_5353_, 3);
                        lean_ctor_set(v___x_5353_, 0, v___x_5365_);
                        v___x_5367_ = v___x_5353_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5369_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5365_);
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
                lean_inc(v___y_5380_);
                v___x_5384_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5384_, 0, v___y_5380_);
                lean_ctor_set(v___x_5384_, 1, v___y_5383_);
                lean_inc_n(v___y_5382_, 2);
                v___x_5385_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5385_, 0, v___x_5384_);
                lean_ctor_set(v___x_5385_, 1, v___y_5382_);
                v___x_5386_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_5376_, v___x_5378_);
                v___x_5387_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5387_, 0, v___x_5385_);
                lean_ctor_set(v___x_5387_, 1, v___x_5386_);
                v___x_5388_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5388_, 0, v___x_5387_);
                lean_ctor_set(v___x_5388_, 1, v___y_5382_);
                v___x_5389_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_5377_, v___x_5378_);
                v___x_5390_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5390_, 0, v___x_5388_);
                lean_ctor_set(v___x_5390_, 1, v___x_5389_);
                lean_inc(v___y_5381_);
                v___x_5391_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5391_, 0, v___y_5381_);
                lean_ctor_set(v___x_5391_, 1, v___x_5390_);
                v___x_5392_ = 0;
                v___x_5393_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5393_, 0, v___x_5391_);
                lean_ctor_set_uint8(
                    v___x_5393_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5392_,
                );
                v___x_5394_ = l_Repr_addAppParen(v___x_5393_, v_prec_5341_);
                return v___x_5394_;
            }
            7 => {
                v___x_5397_ = lean_box(1);
                v___x_5398_ = l_Lean_Grind_CommRing_instReprPoly_repr___closed__5;
                v___x_5399_ = lean_obj_once(
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
                    lean_dec(v_k_5375_);
                    v___x_5402_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_5402_, 0, v___x_5401_);
                    v___y_5380_ = v___x_5398_;
                    v___y_5381_ = v___y_5396_;
                    v___y_5382_ = v___x_5397_;
                    v___y_5383_ = v___x_5402_;
                    state = 6;
                    continue;
                } else {
                    v___x_5403_ = l_Int_repr(v_k_5375_);
                    lean_dec(v_k_5375_);
                    v___x_5404_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_5404_, 0, v___x_5403_);
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
    mut v_x_5409_: *mut LeanObject,
    mut v_prec_5410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5411_: *mut LeanObject = core::ptr::null_mut();
    v_res_5411_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_5409_, v_prec_5410_);
    lean_dec(v_prec_5410_);
    return v_res_5411_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0() -> *mut LeanObject
{
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    v___x_5414_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5415_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5415_, 0, v___x_5414_);
    return v___x_5415_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedPoly_default() -> *mut LeanObject {
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    v___x_5416_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    return v___x_5416_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_instInhabitedPoly() -> *mut LeanObject {
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    v___x_5417_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
    return v___x_5417_;
}
pub unsafe fn l_Lean_Grind_CommRing_instHashablePoly_hash(mut v_x_5418_: *mut LeanObject) -> u64 {
    let mut v_k_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: u64 = 0;
    let mut v_intZero_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_5422_: u8 = 0;
    let mut v_a_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: u64 = 0;
    let mut v___x_5427_: u64 = 0;
    let mut v_abs_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: u64 = 0;
    let mut v___x_5435_: u64 = 0;
    let mut v_k_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: u64 = 0;
    let mut v___y_5441_: u64 = 0;
    let mut v___x_5442_: u64 = 0;
    let mut v___x_5443_: u64 = 0;
    let mut v___x_5444_: u64 = 0;
    let mut v___x_5445_: u64 = 0;
    let mut v___x_5446_: u64 = 0;
    let mut v_intZero_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_5448_: u8 = 0;
    let mut v_a_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u64 = 0;
    let mut v_abs_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5418_) == 0 {
                    v_k_5419_ = lean_ctor_get(v_x_5418_, 0);
                    v___x_5420_ = 0u64;
                    v_intZero_5421_ = lean_obj_once(
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
                        v___x_5424_ = lean_unsigned_to_nat(2);
                        v___x_5425_ = lean_nat_mul(v___x_5424_, v_a_5423_);
                        lean_dec(v_a_5423_);
                        v___x_5426_ = lean_uint64_of_nat(v___x_5425_);
                        lean_dec(v___x_5425_);
                        v___x_5427_ = lean_uint64_mix_hash(v___x_5420_, v___x_5426_);
                        return v___x_5427_;
                    } else {
                        v_abs_5428_ = lean_nat_abs(v_k_5419_);
                        v_one_5429_ = lean_unsigned_to_nat(1);
                        v_a_5430_ = lean_nat_sub(v_abs_5428_, v_one_5429_);
                        lean_dec(v_abs_5428_);
                        v___x_5431_ = lean_unsigned_to_nat(2);
                        v___x_5432_ = lean_nat_mul(v___x_5431_, v_a_5430_);
                        lean_dec(v_a_5430_);
                        v___x_5433_ = lean_nat_add(v___x_5432_, v_one_5429_);
                        lean_dec(v___x_5432_);
                        v___x_5434_ = lean_uint64_of_nat(v___x_5433_);
                        lean_dec(v___x_5433_);
                        v___x_5435_ = lean_uint64_mix_hash(v___x_5420_, v___x_5434_);
                        return v___x_5435_;
                    }
                } else {
                    v_k_5436_ = lean_ctor_get(v_x_5418_, 0);
                    v_v_5437_ = lean_ctor_get(v_x_5418_, 1);
                    v_p_5438_ = lean_ctor_get(v_x_5418_, 2);
                    v___x_5439_ = 1u64;
                    v_intZero_5447_ = lean_obj_once(
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
                        v___x_5450_ = lean_unsigned_to_nat(2);
                        v___x_5451_ = lean_nat_mul(v___x_5450_, v_a_5449_);
                        lean_dec(v_a_5449_);
                        v___x_5452_ = lean_uint64_of_nat(v___x_5451_);
                        lean_dec(v___x_5451_);
                        v___y_5441_ = v___x_5452_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_5453_ = lean_nat_abs(v_k_5436_);
                        v_one_5454_ = lean_unsigned_to_nat(1);
                        v_a_5455_ = lean_nat_sub(v_abs_5453_, v_one_5454_);
                        lean_dec(v_abs_5453_);
                        v___x_5456_ = lean_unsigned_to_nat(2);
                        v___x_5457_ = lean_nat_mul(v___x_5456_, v_a_5455_);
                        lean_dec(v_a_5455_);
                        v___x_5458_ = lean_nat_add(v___x_5457_, v_one_5454_);
                        lean_dec(v___x_5457_);
                        v___x_5459_ = lean_uint64_of_nat(v___x_5458_);
                        lean_dec(v___x_5458_);
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
    mut v_x_5460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5461_: u64 = 0;
    let mut v_r_5462_: *mut LeanObject = core::ptr::null_mut();
    v_res_5461_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_5460_);
    lean_dec_ref(v_x_5460_);
    v_r_5462_ = lean_box_uint64(v_res_5461_);
    return v_r_5462_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote___redArg(
    mut v_inst_5465_: *mut LeanObject,
    mut v_ctx_5466_: *mut LeanObject,
    mut v_p_5467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCast_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAdd_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    v_toSemiring_5468_ = lean_ctor_get(v_inst_5465_, 0);
    v_intCast_5469_ = lean_ctor_get(v_inst_5465_, 3);
    v_toAdd_5470_ = lean_ctor_get(v_toSemiring_5468_, 0);
    lean_inc(v_toAdd_5470_);
    lean_inc_ref(v_inst_5465_);
    v___x_5471_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5465_);
    if lean_obj_tag(v_p_5467_) == 0 {
        let mut v_k_5472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_intCast_5469_);
        lean_dec_ref(v___x_5471_);
        lean_dec(v_toAdd_5470_);
        lean_dec_ref(v_inst_5465_);
        v_k_5472_ = lean_ctor_get(v_p_5467_, 0);
        lean_inc(v_k_5472_);
        lean_dec_ref_known(v_p_5467_, 1);
        v___x_5473_ = lean_apply_1(v_intCast_5469_, v_k_5472_);
        return v___x_5473_;
    } else {
        let mut v_zsmul_5474_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5475_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5476_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
        v_zsmul_5474_ = lean_ctor_get(v___x_5471_, 2);
        lean_inc(v_zsmul_5474_);
        lean_dec_ref(v___x_5471_);
        v_k_5475_ = lean_ctor_get(v_p_5467_, 0);
        lean_inc(v_k_5475_);
        v_v_5476_ = lean_ctor_get(v_p_5467_, 1);
        lean_inc(v_v_5476_);
        v_p_5477_ = lean_ctor_get(v_p_5467_, 2);
        lean_inc_ref(v_p_5477_);
        lean_dec_ref_known(v_p_5467_, 3);
        lean_inc_ref(v_toSemiring_5468_);
        v___x_5478_ =
            l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_5468_, v_ctx_5466_, v_v_5476_);
        v___x_5479_ = lean_apply_2(v_zsmul_5474_, v_k_5475_, v___x_5478_);
        v___x_5480_ =
            l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_5465_, v_ctx_5466_, v_p_5477_);
        v___x_5481_ = lean_apply_2(v_toAdd_5470_, v___x_5479_, v___x_5480_);
        return v___x_5481_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(
    mut v_inst_5482_: *mut LeanObject,
    mut v_ctx_5483_: *mut LeanObject,
    mut v_p_5484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5485_: *mut LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_5482_, v_ctx_5483_, v_p_5484_);
    lean_dec_ref(v_ctx_5483_);
    return v_res_5485_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote(
    mut v_00_u03b1_5486_: *mut LeanObject,
    mut v_inst_5487_: *mut LeanObject,
    mut v_ctx_5488_: *mut LeanObject,
    mut v_p_5489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_5487_, v_ctx_5488_, v_p_5489_);
    return v___x_5490_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote___boxed(
    mut v_00_u03b1_5491_: *mut LeanObject,
    mut v_inst_5492_: *mut LeanObject,
    mut v_ctx_5493_: *mut LeanObject,
    mut v_p_5494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5495_: *mut LeanObject = core::ptr::null_mut();
    v_res_5495_ =
        l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_5491_, v_inst_5492_, v_ctx_5493_, v_p_5494_);
    lean_dec_ref(v_ctx_5493_);
    return v_res_5495_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteTerm___redArg(
    mut v_inst_5496_: *mut LeanObject,
    mut v_ctx_5497_: *mut LeanObject,
    mut v_k_5498_: *mut LeanObject,
    mut v_m_5499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmul_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: u8 = 0;
    v_toSemiring_5500_ = lean_ctor_get(v_inst_5496_, 0);
    lean_inc_ref(v_toSemiring_5500_);
    v___x_5501_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5496_);
    v_zsmul_5502_ = lean_ctor_get(v___x_5501_, 2);
    lean_inc(v_zsmul_5502_);
    lean_dec_ref(v___x_5501_);
    v___x_5503_ = lean_unsigned_to_nat(1);
    v___x_5504_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_5505_ = lean_int_dec_eq(v_k_5498_, v___x_5504_);
    if v___x_5505_ == 0 {
        if lean_obj_tag(v_m_5499_) == 0 {
            let mut v_ofNat_5506_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
            v_ofNat_5506_ = lean_ctor_get(v_toSemiring_5500_, 3);
            lean_inc(v_ofNat_5506_);
            lean_dec_ref(v_toSemiring_5500_);
            v___x_5507_ = lean_apply_1(v_ofNat_5506_, v___x_5503_);
            v___x_5508_ = lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5507_);
            return v___x_5508_;
        } else {
            let mut v_p_5509_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5510_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5511_: *mut LeanObject = core::ptr::null_mut();
            let mut v_npow_5512_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5513_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5516_: u8 = 0;
            v_p_5509_ = lean_ctor_get(v_m_5499_, 0);
            lean_inc_ref(v_p_5509_);
            v_m_5510_ = lean_ctor_get(v_m_5499_, 1);
            lean_inc(v_m_5510_);
            lean_dec_ref_known(v_m_5499_, 2);
            v_ofNat_5511_ = lean_ctor_get(v_toSemiring_5500_, 3);
            v_npow_5512_ = lean_ctor_get(v_toSemiring_5500_, 5);
            v_x_5513_ = lean_ctor_get(v_p_5509_, 0);
            lean_inc(v_x_5513_);
            v_k_5514_ = lean_ctor_get(v_p_5509_, 1);
            lean_inc(v_k_5514_);
            lean_dec_ref(v_p_5509_);
            v___x_5515_ = lean_unsigned_to_nat(0);
            v___x_5516_ = lean_nat_dec_eq(v_k_5514_, v___x_5515_);
            if v___x_5516_ == 0 {
                let mut v___x_5517_: u8 = 0;
                v___x_5517_ = lean_nat_dec_eq(v_k_5514_, v___x_5503_);
                if v___x_5517_ == 0 {
                    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5518_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5513_);
                    lean_dec(v_x_5513_);
                    lean_inc(v_npow_5512_);
                    v___x_5519_ = lean_apply_2(v_npow_5512_, v___x_5518_, v_k_5514_);
                    v___x_5520_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5510_,
                        v___x_5519_,
                    );
                    v___x_5521_ = lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5520_);
                    return v___x_5521_;
                } else {
                    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5514_);
                    v___x_5522_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5513_);
                    lean_dec(v_x_5513_);
                    v___x_5523_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5510_,
                        v___x_5522_,
                    );
                    v___x_5524_ = lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5523_);
                    return v___x_5524_;
                }
            } else {
                let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_5514_);
                lean_dec(v_x_5513_);
                lean_inc(v_ofNat_5511_);
                v___x_5525_ = lean_apply_1(v_ofNat_5511_, v___x_5503_);
                v___x_5526_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_toSemiring_5500_,
                    v_ctx_5497_,
                    v_m_5510_,
                    v___x_5525_,
                );
                v___x_5527_ = lean_apply_2(v_zsmul_5502_, v_k_5498_, v___x_5526_);
                return v___x_5527_;
            }
        }
    } else {
        lean_dec(v_zsmul_5502_);
        lean_dec(v_k_5498_);
        if lean_obj_tag(v_m_5499_) == 0 {
            let mut v_ofNat_5528_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
            v_ofNat_5528_ = lean_ctor_get(v_toSemiring_5500_, 3);
            lean_inc(v_ofNat_5528_);
            lean_dec_ref(v_toSemiring_5500_);
            v___x_5529_ = lean_apply_1(v_ofNat_5528_, v___x_5503_);
            return v___x_5529_;
        } else {
            let mut v_p_5530_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5531_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5532_: *mut LeanObject = core::ptr::null_mut();
            let mut v_npow_5533_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5534_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5535_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5537_: u8 = 0;
            v_p_5530_ = lean_ctor_get(v_m_5499_, 0);
            lean_inc_ref(v_p_5530_);
            v_m_5531_ = lean_ctor_get(v_m_5499_, 1);
            lean_inc(v_m_5531_);
            lean_dec_ref_known(v_m_5499_, 2);
            v_ofNat_5532_ = lean_ctor_get(v_toSemiring_5500_, 3);
            v_npow_5533_ = lean_ctor_get(v_toSemiring_5500_, 5);
            v_x_5534_ = lean_ctor_get(v_p_5530_, 0);
            lean_inc(v_x_5534_);
            v_k_5535_ = lean_ctor_get(v_p_5530_, 1);
            lean_inc(v_k_5535_);
            lean_dec_ref(v_p_5530_);
            v___x_5536_ = lean_unsigned_to_nat(0);
            v___x_5537_ = lean_nat_dec_eq(v_k_5535_, v___x_5536_);
            if v___x_5537_ == 0 {
                let mut v___x_5538_: u8 = 0;
                v___x_5538_ = lean_nat_dec_eq(v_k_5535_, v___x_5503_);
                if v___x_5538_ == 0 {
                    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5539_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5534_);
                    lean_dec(v_x_5534_);
                    lean_inc(v_npow_5533_);
                    v___x_5540_ = lean_apply_2(v_npow_5533_, v___x_5539_, v_k_5535_);
                    v___x_5541_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5531_,
                        v___x_5540_,
                    );
                    return v___x_5541_;
                } else {
                    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5535_);
                    v___x_5542_ = l_Lean_RArray_getImpl___redArg(v_ctx_5497_, v_x_5534_);
                    lean_dec(v_x_5534_);
                    v___x_5543_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5500_,
                        v_ctx_5497_,
                        v_m_5531_,
                        v___x_5542_,
                    );
                    return v___x_5543_;
                }
            } else {
                let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_5535_);
                lean_dec(v_x_5534_);
                lean_inc(v_ofNat_5532_);
                v___x_5544_ = lean_apply_1(v_ofNat_5532_, v___x_5503_);
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
    mut v_inst_5546_: *mut LeanObject,
    mut v_ctx_5547_: *mut LeanObject,
    mut v_k_5548_: *mut LeanObject,
    mut v_m_5549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5550_: *mut LeanObject = core::ptr::null_mut();
    v_res_5550_ =
        l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_5546_, v_ctx_5547_, v_k_5548_, v_m_5549_);
    lean_dec_ref(v_ctx_5547_);
    return v_res_5550_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteTerm(
    mut v_00_u03b1_5551_: *mut LeanObject,
    mut v_inst_5552_: *mut LeanObject,
    mut v_ctx_5553_: *mut LeanObject,
    mut v_k_5554_: *mut LeanObject,
    mut v_m_5555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmul_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: u8 = 0;
    v_toSemiring_5556_ = lean_ctor_get(v_inst_5552_, 0);
    lean_inc_ref(v_toSemiring_5556_);
    v___x_5557_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5552_);
    v_zsmul_5558_ = lean_ctor_get(v___x_5557_, 2);
    lean_inc(v_zsmul_5558_);
    lean_dec_ref(v___x_5557_);
    v___x_5559_ = lean_unsigned_to_nat(1);
    v___x_5560_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_5561_ = lean_int_dec_eq(v_k_5554_, v___x_5560_);
    if v___x_5561_ == 0 {
        if lean_obj_tag(v_m_5555_) == 0 {
            let mut v_ofNat_5562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
            v_ofNat_5562_ = lean_ctor_get(v_toSemiring_5556_, 3);
            lean_inc(v_ofNat_5562_);
            lean_dec_ref(v_toSemiring_5556_);
            v___x_5563_ = lean_apply_1(v_ofNat_5562_, v___x_5559_);
            v___x_5564_ = lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5563_);
            return v___x_5564_;
        } else {
            let mut v_p_5565_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5566_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5567_: *mut LeanObject = core::ptr::null_mut();
            let mut v_npow_5568_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5569_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5570_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5572_: u8 = 0;
            v_p_5565_ = lean_ctor_get(v_m_5555_, 0);
            lean_inc_ref(v_p_5565_);
            v_m_5566_ = lean_ctor_get(v_m_5555_, 1);
            lean_inc(v_m_5566_);
            lean_dec_ref_known(v_m_5555_, 2);
            v_ofNat_5567_ = lean_ctor_get(v_toSemiring_5556_, 3);
            v_npow_5568_ = lean_ctor_get(v_toSemiring_5556_, 5);
            v_x_5569_ = lean_ctor_get(v_p_5565_, 0);
            lean_inc(v_x_5569_);
            v_k_5570_ = lean_ctor_get(v_p_5565_, 1);
            lean_inc(v_k_5570_);
            lean_dec_ref(v_p_5565_);
            v___x_5571_ = lean_unsigned_to_nat(0);
            v___x_5572_ = lean_nat_dec_eq(v_k_5570_, v___x_5571_);
            if v___x_5572_ == 0 {
                let mut v___x_5573_: u8 = 0;
                v___x_5573_ = lean_nat_dec_eq(v_k_5570_, v___x_5559_);
                if v___x_5573_ == 0 {
                    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5574_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5569_);
                    lean_dec(v_x_5569_);
                    lean_inc(v_npow_5568_);
                    v___x_5575_ = lean_apply_2(v_npow_5568_, v___x_5574_, v_k_5570_);
                    v___x_5576_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5566_,
                        v___x_5575_,
                    );
                    v___x_5577_ = lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5576_);
                    return v___x_5577_;
                } else {
                    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5570_);
                    v___x_5578_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5569_);
                    lean_dec(v_x_5569_);
                    v___x_5579_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5566_,
                        v___x_5578_,
                    );
                    v___x_5580_ = lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5579_);
                    return v___x_5580_;
                }
            } else {
                let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_5570_);
                lean_dec(v_x_5569_);
                lean_inc(v_ofNat_5567_);
                v___x_5581_ = lean_apply_1(v_ofNat_5567_, v___x_5559_);
                v___x_5582_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                    v_toSemiring_5556_,
                    v_ctx_5553_,
                    v_m_5566_,
                    v___x_5581_,
                );
                v___x_5583_ = lean_apply_2(v_zsmul_5558_, v_k_5554_, v___x_5582_);
                return v___x_5583_;
            }
        }
    } else {
        lean_dec(v_zsmul_5558_);
        lean_dec(v_k_5554_);
        if lean_obj_tag(v_m_5555_) == 0 {
            let mut v_ofNat_5584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
            v_ofNat_5584_ = lean_ctor_get(v_toSemiring_5556_, 3);
            lean_inc(v_ofNat_5584_);
            lean_dec_ref(v_toSemiring_5556_);
            v___x_5585_ = lean_apply_1(v_ofNat_5584_, v___x_5559_);
            return v___x_5585_;
        } else {
            let mut v_p_5586_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_5587_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ofNat_5588_: *mut LeanObject = core::ptr::null_mut();
            let mut v_npow_5589_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5590_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_5591_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5593_: u8 = 0;
            v_p_5586_ = lean_ctor_get(v_m_5555_, 0);
            lean_inc_ref(v_p_5586_);
            v_m_5587_ = lean_ctor_get(v_m_5555_, 1);
            lean_inc(v_m_5587_);
            lean_dec_ref_known(v_m_5555_, 2);
            v_ofNat_5588_ = lean_ctor_get(v_toSemiring_5556_, 3);
            v_npow_5589_ = lean_ctor_get(v_toSemiring_5556_, 5);
            v_x_5590_ = lean_ctor_get(v_p_5586_, 0);
            lean_inc(v_x_5590_);
            v_k_5591_ = lean_ctor_get(v_p_5586_, 1);
            lean_inc(v_k_5591_);
            lean_dec_ref(v_p_5586_);
            v___x_5592_ = lean_unsigned_to_nat(0);
            v___x_5593_ = lean_nat_dec_eq(v_k_5591_, v___x_5592_);
            if v___x_5593_ == 0 {
                let mut v___x_5594_: u8 = 0;
                v___x_5594_ = lean_nat_dec_eq(v_k_5591_, v___x_5559_);
                if v___x_5594_ == 0 {
                    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5595_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5590_);
                    lean_dec(v_x_5590_);
                    lean_inc(v_npow_5589_);
                    v___x_5596_ = lean_apply_2(v_npow_5589_, v___x_5595_, v_k_5591_);
                    v___x_5597_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5587_,
                        v___x_5596_,
                    );
                    return v___x_5597_;
                } else {
                    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5591_);
                    v___x_5598_ = l_Lean_RArray_getImpl___redArg(v_ctx_5553_, v_x_5590_);
                    lean_dec(v_x_5590_);
                    v___x_5599_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5556_,
                        v_ctx_5553_,
                        v_m_5587_,
                        v___x_5598_,
                    );
                    return v___x_5599_;
                }
            } else {
                let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_5591_);
                lean_dec(v_x_5590_);
                lean_inc(v_ofNat_5588_);
                v___x_5600_ = lean_apply_1(v_ofNat_5588_, v___x_5559_);
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
    mut v_00_u03b1_5602_: *mut LeanObject,
    mut v_inst_5603_: *mut LeanObject,
    mut v_ctx_5604_: *mut LeanObject,
    mut v_k_5605_: *mut LeanObject,
    mut v_m_5606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5607_: *mut LeanObject = core::ptr::null_mut();
    v_res_5607_ = l_Lean_Grind_CommRing_denoteTerm(
        v_00_u03b1_5602_,
        v_inst_5603_,
        v_ctx_5604_,
        v_k_5605_,
        v_m_5606_,
    );
    lean_dec_ref(v_ctx_5604_);
    return v_res_5607_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
    mut v_inst_5608_: *mut LeanObject,
    mut v_ctx_5609_: *mut LeanObject,
    mut v_p_5610_: *mut LeanObject,
    mut v_acc_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCast_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAdd_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: u8 = 0;
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAdd_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNat_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmul_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: u8 = 0;
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: u8 = 0;
    let mut v___x_5644_: u8 = 0;
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: u8 = 0;
    let mut v___x_5662_: u8 = 0;
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_5610_) == 0 {
                    v_toSemiring_5612_ = lean_ctor_get(v_inst_5608_, 0);
                    lean_inc_ref(v_toSemiring_5612_);
                    v_intCast_5613_ = lean_ctor_get(v_inst_5608_, 3);
                    lean_inc(v_intCast_5613_);
                    lean_dec_ref(v_inst_5608_);
                    v_toAdd_5614_ = lean_ctor_get(v_toSemiring_5612_, 0);
                    lean_inc(v_toAdd_5614_);
                    lean_dec_ref(v_toSemiring_5612_);
                    v_k_5615_ = lean_ctor_get(v_p_5610_, 0);
                    lean_inc(v_k_5615_);
                    lean_dec_ref_known(v_p_5610_, 1);
                    v___x_5616_ = lean_obj_once(
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
                        v___x_5618_ = lean_apply_1(v_intCast_5613_, v_k_5615_);
                        v___x_5619_ = lean_apply_2(v_toAdd_5614_, v_acc_5611_, v___x_5618_);
                        return v___x_5619_;
                    } else {
                        lean_dec(v_k_5615_);
                        lean_dec(v_toAdd_5614_);
                        lean_dec(v_intCast_5613_);
                        return v_acc_5611_;
                    }
                } else {
                    v_toSemiring_5620_ = lean_ctor_get(v_inst_5608_, 0);
                    v_toAdd_5621_ = lean_ctor_get(v_toSemiring_5620_, 0);
                    v_ofNat_5622_ = lean_ctor_get(v_toSemiring_5620_, 3);
                    v_npow_5623_ = lean_ctor_get(v_toSemiring_5620_, 5);
                    v_k_5624_ = lean_ctor_get(v_p_5610_, 0);
                    lean_inc(v_k_5624_);
                    v_v_5625_ = lean_ctor_get(v_p_5610_, 1);
                    lean_inc(v_v_5625_);
                    v_p_5626_ = lean_ctor_get(v_p_5610_, 2);
                    lean_inc_ref(v_p_5626_);
                    lean_dec_ref_known(v_p_5610_, 3);
                    lean_inc_ref(v_inst_5608_);
                    v___x_5631_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5608_);
                    v_zsmul_5632_ = lean_ctor_get(v___x_5631_, 2);
                    lean_inc(v_zsmul_5632_);
                    lean_dec_ref(v___x_5631_);
                    v___x_5633_ = lean_unsigned_to_nat(1);
                    v___x_5634_ = lean_obj_once(
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
                        if lean_obj_tag(v_v_5625_) == 0 {
                            lean_inc(v_ofNat_5622_);
                            v___x_5636_ = lean_apply_1(v_ofNat_5622_, v___x_5633_);
                            v___x_5637_ = lean_apply_2(v_zsmul_5632_, v_k_5624_, v___x_5636_);
                            v___y_5628_ = v___x_5637_;
                            state = 1;
                            continue;
                        } else {
                            v_p_5638_ = lean_ctor_get(v_v_5625_, 0);
                            lean_inc_ref(v_p_5638_);
                            v_m_5639_ = lean_ctor_get(v_v_5625_, 1);
                            lean_inc(v_m_5639_);
                            lean_dec_ref_known(v_v_5625_, 2);
                            v_x_5640_ = lean_ctor_get(v_p_5638_, 0);
                            lean_inc(v_x_5640_);
                            v_k_5641_ = lean_ctor_get(v_p_5638_, 1);
                            lean_inc(v_k_5641_);
                            lean_dec_ref(v_p_5638_);
                            v___x_5642_ = lean_unsigned_to_nat(0);
                            v___x_5643_ = lean_nat_dec_eq(v_k_5641_, v___x_5642_);
                            if v___x_5643_ == 0 {
                                v___x_5644_ = lean_nat_dec_eq(v_k_5641_, v___x_5633_);
                                if v___x_5644_ == 0 {
                                    v___x_5645_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5640_);
                                    lean_dec(v_x_5640_);
                                    lean_inc(v_npow_5623_);
                                    v___x_5646_ =
                                        lean_apply_2(v_npow_5623_, v___x_5645_, v_k_5641_);
                                    lean_inc_ref(v_toSemiring_5620_);
                                    v___x_5647_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                        v_toSemiring_5620_,
                                        v_ctx_5609_,
                                        v_m_5639_,
                                        v___x_5646_,
                                    );
                                    v___x_5648_ =
                                        lean_apply_2(v_zsmul_5632_, v_k_5624_, v___x_5647_);
                                    v___y_5628_ = v___x_5648_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_k_5641_);
                                    v___x_5649_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5640_);
                                    lean_dec(v_x_5640_);
                                    lean_inc_ref(v_toSemiring_5620_);
                                    v___x_5650_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                        v_toSemiring_5620_,
                                        v_ctx_5609_,
                                        v_m_5639_,
                                        v___x_5649_,
                                    );
                                    v___x_5651_ =
                                        lean_apply_2(v_zsmul_5632_, v_k_5624_, v___x_5650_);
                                    v___y_5628_ = v___x_5651_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_k_5641_);
                                lean_dec(v_x_5640_);
                                lean_inc(v_ofNat_5622_);
                                v___x_5652_ = lean_apply_1(v_ofNat_5622_, v___x_5633_);
                                lean_inc_ref(v_toSemiring_5620_);
                                v___x_5653_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                                    v_toSemiring_5620_,
                                    v_ctx_5609_,
                                    v_m_5639_,
                                    v___x_5652_,
                                );
                                v___x_5654_ = lean_apply_2(v_zsmul_5632_, v_k_5624_, v___x_5653_);
                                v___y_5628_ = v___x_5654_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_zsmul_5632_);
                        lean_dec(v_k_5624_);
                        if lean_obj_tag(v_v_5625_) == 0 {
                            lean_inc(v_ofNat_5622_);
                            v___x_5655_ = lean_apply_1(v_ofNat_5622_, v___x_5633_);
                            v___y_5628_ = v___x_5655_;
                            state = 1;
                            continue;
                        } else {
                            v_p_5656_ = lean_ctor_get(v_v_5625_, 0);
                            lean_inc_ref(v_p_5656_);
                            v_m_5657_ = lean_ctor_get(v_v_5625_, 1);
                            lean_inc(v_m_5657_);
                            lean_dec_ref_known(v_v_5625_, 2);
                            v_x_5658_ = lean_ctor_get(v_p_5656_, 0);
                            lean_inc(v_x_5658_);
                            v_k_5659_ = lean_ctor_get(v_p_5656_, 1);
                            lean_inc(v_k_5659_);
                            lean_dec_ref(v_p_5656_);
                            v___x_5660_ = lean_unsigned_to_nat(0);
                            v___x_5661_ = lean_nat_dec_eq(v_k_5659_, v___x_5660_);
                            if v___x_5661_ == 0 {
                                v___x_5662_ = lean_nat_dec_eq(v_k_5659_, v___x_5633_);
                                if v___x_5662_ == 0 {
                                    v___x_5663_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5658_);
                                    lean_dec(v_x_5658_);
                                    lean_inc(v_npow_5623_);
                                    v___x_5664_ =
                                        lean_apply_2(v_npow_5623_, v___x_5663_, v_k_5659_);
                                    lean_inc_ref(v_toSemiring_5620_);
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
                                    lean_dec(v_k_5659_);
                                    v___x_5666_ =
                                        l_Lean_RArray_getImpl___redArg(v_ctx_5609_, v_x_5658_);
                                    lean_dec(v_x_5658_);
                                    lean_inc_ref(v_toSemiring_5620_);
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
                                lean_dec(v_k_5659_);
                                lean_dec(v_x_5658_);
                                lean_inc(v_ofNat_5622_);
                                v___x_5668_ = lean_apply_1(v_ofNat_5622_, v___x_5633_);
                                lean_inc_ref(v_toSemiring_5620_);
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
                lean_inc(v_toAdd_5621_);
                v___x_5629_ = lean_apply_2(v_toAdd_5621_, v_acc_5611_, v___y_5628_);
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
    mut v_inst_5670_: *mut LeanObject,
    mut v_ctx_5671_: *mut LeanObject,
    mut v_p_5672_: *mut LeanObject,
    mut v_acc_5673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5674_: *mut LeanObject = core::ptr::null_mut();
    v_res_5674_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
        v_inst_5670_,
        v_ctx_5671_,
        v_p_5672_,
        v_acc_5673_,
    );
    lean_dec_ref(v_ctx_5671_);
    return v_res_5674_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go(
    mut v_00_u03b1_5675_: *mut LeanObject,
    mut v_inst_5676_: *mut LeanObject,
    mut v_ctx_5677_: *mut LeanObject,
    mut v_p_5678_: *mut LeanObject,
    mut v_acc_5679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    v___x_5680_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
        v_inst_5676_,
        v_ctx_5677_,
        v_p_5678_,
        v_acc_5679_,
    );
    return v___x_5680_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(
    mut v_00_u03b1_5681_: *mut LeanObject,
    mut v_inst_5682_: *mut LeanObject,
    mut v_ctx_5683_: *mut LeanObject,
    mut v_p_5684_: *mut LeanObject,
    mut v_acc_5685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5686_: *mut LeanObject = core::ptr::null_mut();
    v_res_5686_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(
        v_00_u03b1_5681_,
        v_inst_5682_,
        v_ctx_5683_,
        v_p_5684_,
        v_acc_5685_,
    );
    lean_dec_ref(v_ctx_5683_);
    return v_res_5686_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27___redArg(
    mut v_inst_5687_: *mut LeanObject,
    mut v_ctx_5688_: *mut LeanObject,
    mut v_p_5689_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_5689_) == 0 {
        let mut v_intCast_5690_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
        v_intCast_5690_ = lean_ctor_get(v_inst_5687_, 3);
        lean_inc(v_intCast_5690_);
        lean_dec_ref(v_inst_5687_);
        v_k_5691_ = lean_ctor_get(v_p_5689_, 0);
        lean_inc(v_k_5691_);
        lean_dec_ref_known(v_p_5689_, 1);
        v___x_5692_ = lean_apply_1(v_intCast_5690_, v_k_5691_);
        return v___x_5692_;
    } else {
        let mut v_toSemiring_5693_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5694_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5695_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zsmul_5698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5701_: u8 = 0;
        v_toSemiring_5693_ = lean_ctor_get(v_inst_5687_, 0);
        v_k_5694_ = lean_ctor_get(v_p_5689_, 0);
        lean_inc(v_k_5694_);
        v_v_5695_ = lean_ctor_get(v_p_5689_, 1);
        lean_inc(v_v_5695_);
        v_p_5696_ = lean_ctor_get(v_p_5689_, 2);
        lean_inc_ref(v_p_5696_);
        lean_dec_ref_known(v_p_5689_, 3);
        lean_inc_ref(v_inst_5687_);
        v___x_5697_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5687_);
        v_zsmul_5698_ = lean_ctor_get(v___x_5697_, 2);
        lean_inc(v_zsmul_5698_);
        lean_dec_ref(v___x_5697_);
        v___x_5699_ = lean_unsigned_to_nat(1);
        v___x_5700_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_5701_ = lean_int_dec_eq(v_k_5694_, v___x_5700_);
        if v___x_5701_ == 0 {
            if lean_obj_tag(v_v_5695_) == 0 {
                let mut v_ofNat_5702_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
                v_ofNat_5702_ = lean_ctor_get(v_toSemiring_5693_, 3);
                lean_inc(v_ofNat_5702_);
                v___x_5703_ = lean_apply_1(v_ofNat_5702_, v___x_5699_);
                v___x_5704_ = lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5703_);
                v___x_5705_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5687_,
                    v_ctx_5688_,
                    v_p_5696_,
                    v___x_5704_,
                );
                return v___x_5705_;
            } else {
                let mut v_p_5706_: *mut LeanObject = core::ptr::null_mut();
                let mut v_m_5707_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5708_: *mut LeanObject = core::ptr::null_mut();
                let mut v_npow_5709_: *mut LeanObject = core::ptr::null_mut();
                let mut v_x_5710_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_5711_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5713_: u8 = 0;
                v_p_5706_ = lean_ctor_get(v_v_5695_, 0);
                lean_inc_ref(v_p_5706_);
                v_m_5707_ = lean_ctor_get(v_v_5695_, 1);
                lean_inc(v_m_5707_);
                lean_dec_ref_known(v_v_5695_, 2);
                v_ofNat_5708_ = lean_ctor_get(v_toSemiring_5693_, 3);
                v_npow_5709_ = lean_ctor_get(v_toSemiring_5693_, 5);
                v_x_5710_ = lean_ctor_get(v_p_5706_, 0);
                lean_inc(v_x_5710_);
                v_k_5711_ = lean_ctor_get(v_p_5706_, 1);
                lean_inc(v_k_5711_);
                lean_dec_ref(v_p_5706_);
                v___x_5712_ = lean_unsigned_to_nat(0);
                v___x_5713_ = lean_nat_dec_eq(v_k_5711_, v___x_5712_);
                if v___x_5713_ == 0 {
                    let mut v___x_5714_: u8 = 0;
                    v___x_5714_ = lean_nat_dec_eq(v_k_5711_, v___x_5699_);
                    if v___x_5714_ == 0 {
                        let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5715_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5710_);
                        lean_dec(v_x_5710_);
                        lean_inc(v_npow_5709_);
                        v___x_5716_ = lean_apply_2(v_npow_5709_, v___x_5715_, v_k_5711_);
                        lean_inc_ref(v_toSemiring_5693_);
                        v___x_5717_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5693_,
                            v_ctx_5688_,
                            v_m_5707_,
                            v___x_5716_,
                        );
                        v___x_5718_ = lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5717_);
                        v___x_5719_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5687_,
                            v_ctx_5688_,
                            v_p_5696_,
                            v___x_5718_,
                        );
                        return v___x_5719_;
                    } else {
                        let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_k_5711_);
                        v___x_5720_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5710_);
                        lean_dec(v_x_5710_);
                        lean_inc_ref(v_toSemiring_5693_);
                        v___x_5721_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5693_,
                            v_ctx_5688_,
                            v_m_5707_,
                            v___x_5720_,
                        );
                        v___x_5722_ = lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5721_);
                        v___x_5723_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5687_,
                            v_ctx_5688_,
                            v_p_5696_,
                            v___x_5722_,
                        );
                        return v___x_5723_;
                    }
                } else {
                    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5711_);
                    lean_dec(v_x_5710_);
                    lean_inc(v_ofNat_5708_);
                    v___x_5724_ = lean_apply_1(v_ofNat_5708_, v___x_5699_);
                    lean_inc_ref(v_toSemiring_5693_);
                    v___x_5725_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5693_,
                        v_ctx_5688_,
                        v_m_5707_,
                        v___x_5724_,
                    );
                    v___x_5726_ = lean_apply_2(v_zsmul_5698_, v_k_5694_, v___x_5725_);
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
            lean_dec(v_zsmul_5698_);
            lean_dec(v_k_5694_);
            if lean_obj_tag(v_v_5695_) == 0 {
                let mut v_ofNat_5728_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
                v_ofNat_5728_ = lean_ctor_get(v_toSemiring_5693_, 3);
                lean_inc(v_ofNat_5728_);
                v___x_5729_ = lean_apply_1(v_ofNat_5728_, v___x_5699_);
                v___x_5730_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5687_,
                    v_ctx_5688_,
                    v_p_5696_,
                    v___x_5729_,
                );
                return v___x_5730_;
            } else {
                let mut v_p_5731_: *mut LeanObject = core::ptr::null_mut();
                let mut v_m_5732_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5733_: *mut LeanObject = core::ptr::null_mut();
                let mut v_npow_5734_: *mut LeanObject = core::ptr::null_mut();
                let mut v_x_5735_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_5736_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5738_: u8 = 0;
                v_p_5731_ = lean_ctor_get(v_v_5695_, 0);
                lean_inc_ref(v_p_5731_);
                v_m_5732_ = lean_ctor_get(v_v_5695_, 1);
                lean_inc(v_m_5732_);
                lean_dec_ref_known(v_v_5695_, 2);
                v_ofNat_5733_ = lean_ctor_get(v_toSemiring_5693_, 3);
                v_npow_5734_ = lean_ctor_get(v_toSemiring_5693_, 5);
                v_x_5735_ = lean_ctor_get(v_p_5731_, 0);
                lean_inc(v_x_5735_);
                v_k_5736_ = lean_ctor_get(v_p_5731_, 1);
                lean_inc(v_k_5736_);
                lean_dec_ref(v_p_5731_);
                v___x_5737_ = lean_unsigned_to_nat(0);
                v___x_5738_ = lean_nat_dec_eq(v_k_5736_, v___x_5737_);
                if v___x_5738_ == 0 {
                    let mut v___x_5739_: u8 = 0;
                    v___x_5739_ = lean_nat_dec_eq(v_k_5736_, v___x_5699_);
                    if v___x_5739_ == 0 {
                        let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5740_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5735_);
                        lean_dec(v_x_5735_);
                        lean_inc(v_npow_5734_);
                        v___x_5741_ = lean_apply_2(v_npow_5734_, v___x_5740_, v_k_5736_);
                        lean_inc_ref(v_toSemiring_5693_);
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
                        let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_k_5736_);
                        v___x_5744_ = l_Lean_RArray_getImpl___redArg(v_ctx_5688_, v_x_5735_);
                        lean_dec(v_x_5735_);
                        lean_inc_ref(v_toSemiring_5693_);
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
                    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5736_);
                    lean_dec(v_x_5735_);
                    lean_inc(v_ofNat_5733_);
                    v___x_5747_ = lean_apply_1(v_ofNat_5733_, v___x_5699_);
                    lean_inc_ref(v_toSemiring_5693_);
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
    mut v_inst_5750_: *mut LeanObject,
    mut v_ctx_5751_: *mut LeanObject,
    mut v_p_5752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5753_: *mut LeanObject = core::ptr::null_mut();
    v_res_5753_ =
        l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_5750_, v_ctx_5751_, v_p_5752_);
    lean_dec_ref(v_ctx_5751_);
    return v_res_5753_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denote_x27(
    mut v_00_u03b1_5754_: *mut LeanObject,
    mut v_inst_5755_: *mut LeanObject,
    mut v_ctx_5756_: *mut LeanObject,
    mut v_p_5757_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_5757_) == 0 {
        let mut v_intCast_5758_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
        v_intCast_5758_ = lean_ctor_get(v_inst_5755_, 3);
        lean_inc(v_intCast_5758_);
        lean_dec_ref(v_inst_5755_);
        v_k_5759_ = lean_ctor_get(v_p_5757_, 0);
        lean_inc(v_k_5759_);
        lean_dec_ref_known(v_p_5757_, 1);
        v___x_5760_ = lean_apply_1(v_intCast_5758_, v_k_5759_);
        return v___x_5760_;
    } else {
        let mut v_toSemiring_5761_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5762_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5763_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zsmul_5766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5769_: u8 = 0;
        v_toSemiring_5761_ = lean_ctor_get(v_inst_5755_, 0);
        v_k_5762_ = lean_ctor_get(v_p_5757_, 0);
        lean_inc(v_k_5762_);
        v_v_5763_ = lean_ctor_get(v_p_5757_, 1);
        lean_inc(v_v_5763_);
        v_p_5764_ = lean_ctor_get(v_p_5757_, 2);
        lean_inc_ref(v_p_5764_);
        lean_dec_ref_known(v_p_5757_, 3);
        lean_inc_ref(v_inst_5755_);
        v___x_5765_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_5755_);
        v_zsmul_5766_ = lean_ctor_get(v___x_5765_, 2);
        lean_inc(v_zsmul_5766_);
        lean_dec_ref(v___x_5765_);
        v___x_5767_ = lean_unsigned_to_nat(1);
        v___x_5768_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_5769_ = lean_int_dec_eq(v_k_5762_, v___x_5768_);
        if v___x_5769_ == 0 {
            if lean_obj_tag(v_v_5763_) == 0 {
                let mut v_ofNat_5770_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
                v_ofNat_5770_ = lean_ctor_get(v_toSemiring_5761_, 3);
                lean_inc(v_ofNat_5770_);
                v___x_5771_ = lean_apply_1(v_ofNat_5770_, v___x_5767_);
                v___x_5772_ = lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5771_);
                v___x_5773_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5755_,
                    v_ctx_5756_,
                    v_p_5764_,
                    v___x_5772_,
                );
                return v___x_5773_;
            } else {
                let mut v_p_5774_: *mut LeanObject = core::ptr::null_mut();
                let mut v_m_5775_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5776_: *mut LeanObject = core::ptr::null_mut();
                let mut v_npow_5777_: *mut LeanObject = core::ptr::null_mut();
                let mut v_x_5778_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_5779_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5781_: u8 = 0;
                v_p_5774_ = lean_ctor_get(v_v_5763_, 0);
                lean_inc_ref(v_p_5774_);
                v_m_5775_ = lean_ctor_get(v_v_5763_, 1);
                lean_inc(v_m_5775_);
                lean_dec_ref_known(v_v_5763_, 2);
                v_ofNat_5776_ = lean_ctor_get(v_toSemiring_5761_, 3);
                v_npow_5777_ = lean_ctor_get(v_toSemiring_5761_, 5);
                v_x_5778_ = lean_ctor_get(v_p_5774_, 0);
                lean_inc(v_x_5778_);
                v_k_5779_ = lean_ctor_get(v_p_5774_, 1);
                lean_inc(v_k_5779_);
                lean_dec_ref(v_p_5774_);
                v___x_5780_ = lean_unsigned_to_nat(0);
                v___x_5781_ = lean_nat_dec_eq(v_k_5779_, v___x_5780_);
                if v___x_5781_ == 0 {
                    let mut v___x_5782_: u8 = 0;
                    v___x_5782_ = lean_nat_dec_eq(v_k_5779_, v___x_5767_);
                    if v___x_5782_ == 0 {
                        let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5783_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5778_);
                        lean_dec(v_x_5778_);
                        lean_inc(v_npow_5777_);
                        v___x_5784_ = lean_apply_2(v_npow_5777_, v___x_5783_, v_k_5779_);
                        lean_inc_ref(v_toSemiring_5761_);
                        v___x_5785_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5761_,
                            v_ctx_5756_,
                            v_m_5775_,
                            v___x_5784_,
                        );
                        v___x_5786_ = lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5785_);
                        v___x_5787_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5755_,
                            v_ctx_5756_,
                            v_p_5764_,
                            v___x_5786_,
                        );
                        return v___x_5787_;
                    } else {
                        let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_k_5779_);
                        v___x_5788_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5778_);
                        lean_dec(v_x_5778_);
                        lean_inc_ref(v_toSemiring_5761_);
                        v___x_5789_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                            v_toSemiring_5761_,
                            v_ctx_5756_,
                            v_m_5775_,
                            v___x_5788_,
                        );
                        v___x_5790_ = lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5789_);
                        v___x_5791_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                            v_inst_5755_,
                            v_ctx_5756_,
                            v_p_5764_,
                            v___x_5790_,
                        );
                        return v___x_5791_;
                    }
                } else {
                    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5779_);
                    lean_dec(v_x_5778_);
                    lean_inc(v_ofNat_5776_);
                    v___x_5792_ = lean_apply_1(v_ofNat_5776_, v___x_5767_);
                    lean_inc_ref(v_toSemiring_5761_);
                    v___x_5793_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(
                        v_toSemiring_5761_,
                        v_ctx_5756_,
                        v_m_5775_,
                        v___x_5792_,
                    );
                    v___x_5794_ = lean_apply_2(v_zsmul_5766_, v_k_5762_, v___x_5793_);
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
            lean_dec(v_zsmul_5766_);
            lean_dec(v_k_5762_);
            if lean_obj_tag(v_v_5763_) == 0 {
                let mut v_ofNat_5796_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
                v_ofNat_5796_ = lean_ctor_get(v_toSemiring_5761_, 3);
                lean_inc(v_ofNat_5796_);
                v___x_5797_ = lean_apply_1(v_ofNat_5796_, v___x_5767_);
                v___x_5798_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(
                    v_inst_5755_,
                    v_ctx_5756_,
                    v_p_5764_,
                    v___x_5797_,
                );
                return v___x_5798_;
            } else {
                let mut v_p_5799_: *mut LeanObject = core::ptr::null_mut();
                let mut v_m_5800_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ofNat_5801_: *mut LeanObject = core::ptr::null_mut();
                let mut v_npow_5802_: *mut LeanObject = core::ptr::null_mut();
                let mut v_x_5803_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_5804_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5806_: u8 = 0;
                v_p_5799_ = lean_ctor_get(v_v_5763_, 0);
                lean_inc_ref(v_p_5799_);
                v_m_5800_ = lean_ctor_get(v_v_5763_, 1);
                lean_inc(v_m_5800_);
                lean_dec_ref_known(v_v_5763_, 2);
                v_ofNat_5801_ = lean_ctor_get(v_toSemiring_5761_, 3);
                v_npow_5802_ = lean_ctor_get(v_toSemiring_5761_, 5);
                v_x_5803_ = lean_ctor_get(v_p_5799_, 0);
                lean_inc(v_x_5803_);
                v_k_5804_ = lean_ctor_get(v_p_5799_, 1);
                lean_inc(v_k_5804_);
                lean_dec_ref(v_p_5799_);
                v___x_5805_ = lean_unsigned_to_nat(0);
                v___x_5806_ = lean_nat_dec_eq(v_k_5804_, v___x_5805_);
                if v___x_5806_ == 0 {
                    let mut v___x_5807_: u8 = 0;
                    v___x_5807_ = lean_nat_dec_eq(v_k_5804_, v___x_5767_);
                    if v___x_5807_ == 0 {
                        let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5808_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5803_);
                        lean_dec(v_x_5803_);
                        lean_inc(v_npow_5802_);
                        v___x_5809_ = lean_apply_2(v_npow_5802_, v___x_5808_, v_k_5804_);
                        lean_inc_ref(v_toSemiring_5761_);
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
                        let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_k_5804_);
                        v___x_5812_ = l_Lean_RArray_getImpl___redArg(v_ctx_5756_, v_x_5803_);
                        lean_dec(v_x_5803_);
                        lean_inc_ref(v_toSemiring_5761_);
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
                    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_k_5804_);
                    lean_dec(v_x_5803_);
                    lean_inc(v_ofNat_5801_);
                    v___x_5815_ = lean_apply_1(v_ofNat_5801_, v___x_5767_);
                    lean_inc_ref(v_toSemiring_5761_);
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
    mut v_00_u03b1_5818_: *mut LeanObject,
    mut v_inst_5819_: *mut LeanObject,
    mut v_ctx_5820_: *mut LeanObject,
    mut v_p_5821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5822_: *mut LeanObject = core::ptr::null_mut();
    v_res_5822_ = l_Lean_Grind_CommRing_Poly_denote_x27(
        v_00_u03b1_5818_,
        v_inst_5819_,
        v_ctx_5820_,
        v_p_5821_,
    );
    lean_dec_ref(v_ctx_5820_);
    return v_res_5822_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ofMon(mut v_m_5823_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    v___x_5824_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_5825_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_5826_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5826_, 0, v___x_5824_);
    lean_ctor_set(v___x_5826_, 1, v_m_5823_);
    lean_ctor_set(v___x_5826_, 2, v___x_5825_);
    return v___x_5826_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_ofVar(mut v_x_5827_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_5827_);
    v___x_5829_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_5828_);
    return v___x_5829_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_isSorted(mut v_x_5830_: *mut LeanObject) -> u8 {
    let mut v___x_5831_: u8 = 0;
    let mut v_p_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: u8 = 0;
    let mut v_v_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: u8 = 0;
    let mut v___x_5837_: u8 = 0;
    let mut v___x_5838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5830_) == 0 {
                    v___x_5831_ = 1;
                    return v___x_5831_;
                } else {
                    v_p_5832_ = lean_ctor_get(v_x_5830_, 2);
                    if lean_obj_tag(v_p_5832_) == 0 {
                        v___x_5833_ = 1;
                        return v___x_5833_;
                    } else {
                        v_v_5834_ = lean_ctor_get(v_x_5830_, 1);
                        v_v_5835_ = lean_ctor_get(v_p_5832_, 1);
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
    mut v_x_5840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5841_: u8 = 0;
    let mut v_r_5842_: *mut LeanObject = core::ptr::null_mut();
    v_res_5841_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_5840_);
    lean_dec_ref(v_x_5840_);
    v_r_5842_ = lean_box((v_res_5841_) as usize);
    return v_r_5842_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst_go(
    mut v_k_5843_: *mut LeanObject,
    mut v_a_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5848_: u8 = 0;
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5853_: u8 = 0;
    let mut v_k_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5859_: u8 = 0;
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5844_) == 0 {
                    v_k_5845_ = lean_ctor_get(v_a_5844_, 0);
                    v_isSharedCheck_5853_ = (!lean_is_exclusive(v_a_5844_)) as u8;
                    if v_isSharedCheck_5853_ == 0 {
                        v___x_5847_ = v_a_5844_;
                        v_isShared_5848_ = v_isSharedCheck_5853_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_5845_);
                        lean_dec(v_a_5844_);
                        v___x_5847_ = lean_box(0);
                        v_isShared_5848_ = v_isSharedCheck_5853_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5854_ = lean_ctor_get(v_a_5844_, 0);
                    v_v_5855_ = lean_ctor_get(v_a_5844_, 1);
                    v_p_5856_ = lean_ctor_get(v_a_5844_, 2);
                    v_isSharedCheck_5864_ = (!lean_is_exclusive(v_a_5844_)) as u8;
                    if v_isSharedCheck_5864_ == 0 {
                        v___x_5858_ = v_a_5844_;
                        v_isShared_5859_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_p_5856_);
                        lean_inc(v_v_5855_);
                        lean_inc(v_k_5854_);
                        lean_dec(v_a_5844_);
                        v___x_5858_ = lean_box(0);
                        v_isShared_5859_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5849_ = lean_int_add(v_k_5845_, v_k_5843_);
                lean_dec(v_k_5845_);
                if v_isShared_5848_ == 0 {
                    lean_ctor_set(v___x_5847_, 0, v___x_5849_);
                    v___x_5851_ = v___x_5847_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5849_);
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
                    lean_ctor_set(v___x_5858_, 2, v___x_5860_);
                    v___x_5862_ = v___x_5858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_k_5854_);
                    lean_ctor_set(v_reuseFailAlloc_5863_, 1, v_v_5855_);
                    lean_ctor_set(v_reuseFailAlloc_5863_, 2, v___x_5860_);
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
    mut v_k_5865_: *mut LeanObject,
    mut v_a_5866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5867_: *mut LeanObject = core::ptr::null_mut();
    v_res_5867_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_5865_, v_a_5866_);
    lean_dec(v_k_5865_);
    return v_res_5867_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst(
    mut v_p_5868_: *mut LeanObject,
    mut v_k_5869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: u8 = 0;
    v___x_5870_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5871_ = lean_int_dec_eq(v_k_5869_, v___x_5870_);
    if v___x_5871_ == 0 {
        let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
        v___x_5872_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_5869_, v_p_5868_);
        return v___x_5872_;
    } else {
        return v_p_5868_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_addConst___boxed(
    mut v_p_5873_: *mut LeanObject,
    mut v_k_5874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5875_: *mut LeanObject = core::ptr::null_mut();
    v_res_5875_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_5873_, v_k_5874_);
    lean_dec(v_k_5874_);
    return v_res_5875_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(
    mut v_p_5876_: *mut LeanObject,
    mut v_h__1_5877_: *mut LeanObject,
    mut v_h__2_5878_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_5876_) == 0 {
        let mut v_k_5879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5878_);
        v_k_5879_ = lean_ctor_get(v_p_5876_, 0);
        lean_inc(v_k_5879_);
        lean_dec_ref_known(v_p_5876_, 1);
        v___x_5880_ = lean_apply_1(v_h__1_5877_, v_k_5879_);
        return v___x_5880_;
    } else {
        let mut v_k_5881_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5882_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5877_);
        v_k_5881_ = lean_ctor_get(v_p_5876_, 0);
        lean_inc(v_k_5881_);
        v_v_5882_ = lean_ctor_get(v_p_5876_, 1);
        lean_inc(v_v_5882_);
        v_p_5883_ = lean_ctor_get(v_p_5876_, 2);
        lean_inc_ref(v_p_5883_);
        lean_dec_ref_known(v_p_5876_, 3);
        v___x_5884_ = lean_apply_3(v_h__2_5878_, v_k_5881_, v_v_5882_, v_p_5883_);
        return v___x_5884_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(
    mut v_motive_5885_: *mut LeanObject,
    mut v_p_5886_: *mut LeanObject,
    mut v_h__1_5887_: *mut LeanObject,
    mut v_h__2_5888_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_5886_) == 0 {
        let mut v_k_5889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5888_);
        v_k_5889_ = lean_ctor_get(v_p_5886_, 0);
        lean_inc(v_k_5889_);
        lean_dec_ref_known(v_p_5886_, 1);
        v___x_5890_ = lean_apply_1(v_h__1_5887_, v_k_5889_);
        return v___x_5890_;
    } else {
        let mut v_k_5891_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5892_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5887_);
        v_k_5891_ = lean_ctor_get(v_p_5886_, 0);
        lean_inc(v_k_5891_);
        v_v_5892_ = lean_ctor_get(v_p_5886_, 1);
        lean_inc(v_v_5892_);
        v_p_5893_ = lean_ctor_get(v_p_5886_, 2);
        lean_inc_ref(v_p_5893_);
        lean_dec_ref_known(v_p_5886_, 3);
        v___x_5894_ = lean_apply_3(v_h__2_5888_, v_k_5891_, v_v_5892_, v_p_5893_);
        return v___x_5894_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insert_go(
    mut v_k_5895_: *mut LeanObject,
    mut v_m_5896_: *mut LeanObject,
    mut v_a_5897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: u8 = 0;
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5910_: u8 = 0;
    let mut v_unused_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v_k_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut v_unused_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5897_) == 0 {
                    v___x_5898_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_5898_, 0, v_k_5895_);
                    lean_ctor_set(v___x_5898_, 1, v_m_5896_);
                    lean_ctor_set(v___x_5898_, 2, v_a_5897_);
                    return v___x_5898_;
                } else {
                    v_k_5899_ = lean_ctor_get(v_a_5897_, 0);
                    v_v_5900_ = lean_ctor_get(v_a_5897_, 1);
                    v_p_5901_ = lean_ctor_get(v_a_5897_, 2);
                    v___x_5902_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_5896_, v_v_5900_);
                    match v___x_5902_ {
                        0 => {
                            lean_inc_ref(v_p_5901_);
                            lean_inc(v_v_5900_);
                            lean_inc(v_k_5899_);
                            v_isSharedCheck_5910_ = (!lean_is_exclusive(v_a_5897_)) as u8;
                            if v_isSharedCheck_5910_ == 0 {
                                v_unused_5911_ = lean_ctor_get(v_a_5897_, 2);
                                lean_dec(v_unused_5911_);
                                v_unused_5912_ = lean_ctor_get(v_a_5897_, 1);
                                lean_dec(v_unused_5912_);
                                v_unused_5913_ = lean_ctor_get(v_a_5897_, 0);
                                lean_dec(v_unused_5913_);
                                v___x_5904_ = v_a_5897_;
                                v_isShared_5905_ = v_isSharedCheck_5910_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_5897_);
                                v___x_5904_ = lean_box(0);
                                v_isShared_5905_ = v_isSharedCheck_5910_;
                                state = 1;
                                continue;
                            }
                        }
                        1 => {
                            lean_inc_ref(v_p_5901_);
                            lean_inc(v_k_5899_);
                            v_isSharedCheck_5923_ = (!lean_is_exclusive(v_a_5897_)) as u8;
                            if v_isSharedCheck_5923_ == 0 {
                                v_unused_5924_ = lean_ctor_get(v_a_5897_, 2);
                                lean_dec(v_unused_5924_);
                                v_unused_5925_ = lean_ctor_get(v_a_5897_, 1);
                                lean_dec(v_unused_5925_);
                                v_unused_5926_ = lean_ctor_get(v_a_5897_, 0);
                                lean_dec(v_unused_5926_);
                                v___x_5915_ = v_a_5897_;
                                v_isShared_5916_ = v_isSharedCheck_5923_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_a_5897_);
                                v___x_5915_ = lean_box(0);
                                v_isShared_5916_ = v_isSharedCheck_5923_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            v___x_5927_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_5927_, 0, v_k_5895_);
                            lean_ctor_set(v___x_5927_, 1, v_m_5896_);
                            lean_ctor_set(v___x_5927_, 2, v_a_5897_);
                            return v___x_5927_;
                        }
                    }
                }
            }
            1 => {
                v___x_5906_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_5895_, v_m_5896_, v_p_5901_);
                if v_isShared_5905_ == 0 {
                    lean_ctor_set(v___x_5904_, 2, v___x_5906_);
                    v___x_5908_ = v___x_5904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5909_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_k_5899_);
                    lean_ctor_set(v_reuseFailAlloc_5909_, 1, v_v_5900_);
                    lean_ctor_set(v_reuseFailAlloc_5909_, 2, v___x_5906_);
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
                lean_dec(v_k_5899_);
                lean_dec(v_k_5895_);
                v___x_5918_ = lean_obj_once(
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
                        lean_ctor_set(v___x_5915_, 1, v_m_5896_);
                        lean_ctor_set(v___x_5915_, 0, v_k_5917_);
                        v___x_5921_ = v___x_5915_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_k_5917_);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 1, v_m_5896_);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 2, v_p_5901_);
                        v___x_5921_ = v_reuseFailAlloc_5922_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_k_5917_);
                    lean_del_object(v___x_5915_);
                    lean_dec(v_m_5896_);
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
    mut v_k_5928_: *mut LeanObject,
    mut v_m_5929_: *mut LeanObject,
    mut v_p_5930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: u8 = 0;
    v___x_5931_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5932_ = lean_int_dec_eq(v_k_5928_, v___x_5931_);
    if v___x_5932_ == 0 {
        let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5934_: u8 = 0;
        v___x_5933_ = lean_box(0);
        v___x_5934_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_5929_, v___x_5933_);
        if v___x_5934_ == 0 {
            let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
            v___x_5935_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_5928_, v_m_5929_, v_p_5930_);
            return v___x_5935_;
        } else {
            let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_m_5929_);
            v___x_5936_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_5930_, v_k_5928_);
            lean_dec(v_k_5928_);
            return v___x_5936_;
        }
    } else {
        lean_dec(v_m_5929_);
        lean_dec(v_k_5928_);
        return v_p_5930_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_concat(
    mut v_p_u2081_5937_: *mut LeanObject,
    mut v_p_u2082_5938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5946_: u8 = 0;
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_5937_) == 0 {
                    v_k_5939_ = lean_ctor_get(v_p_u2081_5937_, 0);
                    lean_inc(v_k_5939_);
                    lean_dec_ref_known(v_p_u2081_5937_, 1);
                    v___x_5940_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_5938_, v_k_5939_);
                    lean_dec(v_k_5939_);
                    return v___x_5940_;
                } else {
                    v_k_5941_ = lean_ctor_get(v_p_u2081_5937_, 0);
                    v_v_5942_ = lean_ctor_get(v_p_u2081_5937_, 1);
                    v_p_5943_ = lean_ctor_get(v_p_u2081_5937_, 2);
                    v_isSharedCheck_5951_ = (!lean_is_exclusive(v_p_u2081_5937_)) as u8;
                    if v_isSharedCheck_5951_ == 0 {
                        v___x_5945_ = v_p_u2081_5937_;
                        v_isShared_5946_ = v_isSharedCheck_5951_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_5943_);
                        lean_inc(v_v_5942_);
                        lean_inc(v_k_5941_);
                        lean_dec(v_p_u2081_5937_);
                        v___x_5945_ = lean_box(0);
                        v_isShared_5946_ = v_isSharedCheck_5951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5947_ = l_Lean_Grind_CommRing_Poly_concat(v_p_5943_, v_p_u2082_5938_);
                if v_isShared_5946_ == 0 {
                    lean_ctor_set(v___x_5945_, 2, v___x_5947_);
                    v___x_5949_ = v___x_5945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_k_5941_);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 1, v_v_5942_);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 2, v___x_5947_);
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
    mut v_k_5952_: *mut LeanObject,
    mut v_a_5953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut v_k_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5968_: u8 = 0;
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5953_) == 0 {
                    v_k_5954_ = lean_ctor_get(v_a_5953_, 0);
                    v_isSharedCheck_5962_ = (!lean_is_exclusive(v_a_5953_)) as u8;
                    if v_isSharedCheck_5962_ == 0 {
                        v___x_5956_ = v_a_5953_;
                        v_isShared_5957_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_5954_);
                        lean_dec(v_a_5953_);
                        v___x_5956_ = lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5963_ = lean_ctor_get(v_a_5953_, 0);
                    v_v_5964_ = lean_ctor_get(v_a_5953_, 1);
                    v_p_5965_ = lean_ctor_get(v_a_5953_, 2);
                    v_isSharedCheck_5974_ = (!lean_is_exclusive(v_a_5953_)) as u8;
                    if v_isSharedCheck_5974_ == 0 {
                        v___x_5967_ = v_a_5953_;
                        v_isShared_5968_ = v_isSharedCheck_5974_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_p_5965_);
                        lean_inc(v_v_5964_);
                        lean_inc(v_k_5963_);
                        lean_dec(v_a_5953_);
                        v___x_5967_ = lean_box(0);
                        v_isShared_5968_ = v_isSharedCheck_5974_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5958_ = lean_int_mul(v_k_5952_, v_k_5954_);
                lean_dec(v_k_5954_);
                if v_isShared_5957_ == 0 {
                    lean_ctor_set(v___x_5956_, 0, v___x_5958_);
                    v___x_5960_ = v___x_5956_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5958_);
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
                lean_dec(v_k_5963_);
                v___x_5970_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_5952_, v_p_5965_);
                if v_isShared_5968_ == 0 {
                    lean_ctor_set(v___x_5967_, 2, v___x_5970_);
                    lean_ctor_set(v___x_5967_, 0, v___x_5969_);
                    v___x_5972_ = v___x_5967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5973_, 0, v___x_5969_);
                    lean_ctor_set(v_reuseFailAlloc_5973_, 1, v_v_5964_);
                    lean_ctor_set(v_reuseFailAlloc_5973_, 2, v___x_5970_);
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
    mut v_k_5975_: *mut LeanObject,
    mut v_a_5976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5977_: *mut LeanObject = core::ptr::null_mut();
    v_res_5977_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_5975_, v_a_5976_);
    lean_dec(v_k_5975_);
    return v_res_5977_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst(
    mut v_k_5978_: *mut LeanObject,
    mut v_p_5979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    v___x_5980_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_5981_ = lean_int_dec_eq(v_k_5978_, v___x_5980_);
    if v___x_5981_ == 0 {
        let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5983_: u8 = 0;
        v___x_5982_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_5983_ = lean_int_dec_eq(v_k_5978_, v___x_5982_);
        if v___x_5983_ == 0 {
            let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
            v___x_5984_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_5978_, v_p_5979_);
            return v___x_5984_;
        } else {
            return v_p_5979_;
        }
    } else {
        let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_5979_);
        v___x_5985_ = lean_obj_once(
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
    mut v_k_5986_: *mut LeanObject,
    mut v_p_5987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5988_: *mut LeanObject = core::ptr::null_mut();
    v_res_5988_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_5986_, v_p_5987_);
    lean_dec(v_k_5986_);
    return v_res_5988_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_go(
    mut v_k_5989_: *mut LeanObject,
    mut v_m_5990_: *mut LeanObject,
    mut v_a_5991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: u8 = 0;
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5991_) == 0 {
                    v_k_5992_ = lean_ctor_get(v_a_5991_, 0);
                    lean_inc(v_k_5992_);
                    lean_dec_ref_known(v_a_5991_, 1);
                    v___x_5993_ = lean_obj_once(
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
                        lean_dec(v_k_5992_);
                        v___x_5996_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        v___x_5997_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_5997_, 0, v___x_5995_);
                        lean_ctor_set(v___x_5997_, 1, v_m_5990_);
                        lean_ctor_set(v___x_5997_, 2, v___x_5996_);
                        return v___x_5997_;
                    } else {
                        lean_dec(v_k_5992_);
                        lean_dec(v_m_5990_);
                        v___x_5998_ = lean_obj_once(
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
                    v_k_5999_ = lean_ctor_get(v_a_5991_, 0);
                    v_v_6000_ = lean_ctor_get(v_a_5991_, 1);
                    v_p_6001_ = lean_ctor_get(v_a_5991_, 2);
                    v_isSharedCheck_6011_ = (!lean_is_exclusive(v_a_5991_)) as u8;
                    if v_isSharedCheck_6011_ == 0 {
                        v___x_6003_ = v_a_5991_;
                        v_isShared_6004_ = v_isSharedCheck_6011_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_6001_);
                        lean_inc(v_v_6000_);
                        lean_inc(v_k_5999_);
                        lean_dec(v_a_5991_);
                        v___x_6003_ = lean_box(0);
                        v_isShared_6004_ = v_isSharedCheck_6011_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6005_ = lean_int_mul(v_k_5989_, v_k_5999_);
                lean_dec(v_k_5999_);
                lean_inc(v_m_5990_);
                v___x_6006_ = l_Lean_Grind_CommRing_Mon_mul(v_m_5990_, v_v_6000_);
                v___x_6007_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_5989_, v_m_5990_, v_p_6001_);
                if v_isShared_6004_ == 0 {
                    lean_ctor_set(v___x_6003_, 2, v___x_6007_);
                    lean_ctor_set(v___x_6003_, 1, v___x_6006_);
                    lean_ctor_set(v___x_6003_, 0, v___x_6005_);
                    v___x_6009_ = v___x_6003_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6010_, 0, v___x_6005_);
                    lean_ctor_set(v_reuseFailAlloc_6010_, 1, v___x_6006_);
                    lean_ctor_set(v_reuseFailAlloc_6010_, 2, v___x_6007_);
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
    mut v_k_6012_: *mut LeanObject,
    mut v_m_6013_: *mut LeanObject,
    mut v_a_6014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6015_: *mut LeanObject = core::ptr::null_mut();
    v_res_6015_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_6012_, v_m_6013_, v_a_6014_);
    lean_dec(v_k_6012_);
    return v_res_6015_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon(
    mut v_k_6016_: *mut LeanObject,
    mut v_m_6017_: *mut LeanObject,
    mut v_p_6018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: u8 = 0;
    v___x_6019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6020_ = lean_int_dec_eq(v_k_6016_, v___x_6019_);
    if v___x_6020_ == 0 {
        let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6022_: u8 = 0;
        v___x_6021_ = lean_box(0);
        v___x_6022_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6017_, v___x_6021_);
        if v___x_6022_ == 0 {
            let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
            v___x_6023_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_6016_, v_m_6017_, v_p_6018_);
            return v___x_6023_;
        } else {
            let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_m_6017_);
            v___x_6024_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6016_, v_p_6018_);
            return v___x_6024_;
        }
    } else {
        let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_6018_);
        lean_dec(v_m_6017_);
        v___x_6025_ = lean_obj_once(
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
    mut v_k_6026_: *mut LeanObject,
    mut v_m_6027_: *mut LeanObject,
    mut v_p_6028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6029_: *mut LeanObject = core::ptr::null_mut();
    v_res_6029_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_6026_, v_m_6027_, v_p_6028_);
    lean_dec(v_k_6026_);
    return v_res_6029_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon__nc_go(
    mut v_k_6030_: *mut LeanObject,
    mut v_m_6031_: *mut LeanObject,
    mut v_p_6032_: *mut LeanObject,
    mut v_acc_6033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_6032_) == 0 {
                    v_k_6034_ = lean_ctor_get(v_p_6032_, 0);
                    lean_inc(v_k_6034_);
                    lean_dec_ref_known(v_p_6032_, 1);
                    v___x_6035_ = lean_int_mul(v_k_6030_, v_k_6034_);
                    lean_dec(v_k_6034_);
                    v___x_6036_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6035_, v_m_6031_, v_acc_6033_);
                    return v___x_6036_;
                } else {
                    v_k_6037_ = lean_ctor_get(v_p_6032_, 0);
                    lean_inc(v_k_6037_);
                    v_v_6038_ = lean_ctor_get(v_p_6032_, 1);
                    lean_inc(v_v_6038_);
                    v_p_6039_ = lean_ctor_get(v_p_6032_, 2);
                    lean_inc_ref(v_p_6039_);
                    lean_dec_ref_known(v_p_6032_, 3);
                    v___x_6040_ = lean_int_mul(v_k_6030_, v_k_6037_);
                    lean_dec(v_k_6037_);
                    lean_inc(v_m_6031_);
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
    mut v_k_6044_: *mut LeanObject,
    mut v_m_6045_: *mut LeanObject,
    mut v_p_6046_: *mut LeanObject,
    mut v_acc_6047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6048_: *mut LeanObject = core::ptr::null_mut();
    v_res_6048_ =
        l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_6044_, v_m_6045_, v_p_6046_, v_acc_6047_);
    lean_dec(v_k_6044_);
    return v_res_6048_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon__nc(
    mut v_k_6049_: *mut LeanObject,
    mut v_m_6050_: *mut LeanObject,
    mut v_p_6051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: u8 = 0;
    v___x_6052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6053_ = lean_int_dec_eq(v_k_6049_, v___x_6052_);
    if v___x_6053_ == 0 {
        let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6055_: u8 = 0;
        v___x_6054_ = lean_box(0);
        v___x_6055_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6050_, v___x_6054_);
        if v___x_6055_ == 0 {
            let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
            v___x_6056_ = lean_obj_once(
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
            let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_m_6050_);
            v___x_6058_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6049_, v_p_6051_);
            return v___x_6058_;
        }
    } else {
        let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_6051_);
        lean_dec(v_m_6050_);
        v___x_6059_ = lean_obj_once(
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
    mut v_k_6060_: *mut LeanObject,
    mut v_m_6061_: *mut LeanObject,
    mut v_p_6062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6063_: *mut LeanObject = core::ptr::null_mut();
    v_res_6063_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_6060_, v_m_6061_, v_p_6062_);
    lean_dec(v_k_6060_);
    return v_res_6063_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combine_go(
    mut v_fuel_6064_: *mut LeanObject,
    mut v_p_u2081_6065_: *mut LeanObject,
    mut v_p_u2082_6066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6068_: u8 = 0;
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6074_: u8 = 0;
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6079_: u8 = 0;
    let mut v_k_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: u8 = 0;
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6100_: u8 = 0;
    let mut v_unused_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6106_: u8 = 0;
    let mut v_k_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: u8 = 0;
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6115_: u8 = 0;
    let mut v_unused_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut v_unused_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6067_ = lean_unsigned_to_nat(0);
                v_isZero_6068_ = lean_nat_dec_eq(v_fuel_6064_, v_zero_6067_);
                if v_isZero_6068_ == 1 {
                    lean_dec(v_fuel_6064_);
                    v___x_6069_ =
                        l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_6065_, v_p_u2082_6066_);
                    return v___x_6069_;
                } else {
                    if lean_obj_tag(v_p_u2081_6065_) == 0 {
                        lean_dec(v_fuel_6064_);
                        if lean_obj_tag(v_p_u2082_6066_) == 0 {
                            v_k_6070_ = lean_ctor_get(v_p_u2081_6065_, 0);
                            lean_inc(v_k_6070_);
                            lean_dec_ref_known(v_p_u2081_6065_, 1);
                            v_k_6071_ = lean_ctor_get(v_p_u2082_6066_, 0);
                            v_isSharedCheck_6079_ = (!lean_is_exclusive(v_p_u2082_6066_)) as u8;
                            if v_isSharedCheck_6079_ == 0 {
                                v___x_6073_ = v_p_u2082_6066_;
                                v_isShared_6074_ = v_isSharedCheck_6079_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_k_6071_);
                                lean_dec(v_p_u2082_6066_);
                                v___x_6073_ = lean_box(0);
                                v_isShared_6074_ = v_isSharedCheck_6079_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_k_6080_ = lean_ctor_get(v_p_u2081_6065_, 0);
                            lean_inc(v_k_6080_);
                            lean_dec_ref_known(v_p_u2081_6065_, 1);
                            v___x_6081_ =
                                l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_6066_, v_k_6080_);
                            lean_dec(v_k_6080_);
                            return v___x_6081_;
                        }
                    } else {
                        if lean_obj_tag(v_p_u2082_6066_) == 0 {
                            lean_dec(v_fuel_6064_);
                            v_k_6082_ = lean_ctor_get(v_p_u2082_6066_, 0);
                            lean_inc(v_k_6082_);
                            lean_dec_ref_known(v_p_u2082_6066_, 1);
                            v___x_6083_ =
                                l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_6065_, v_k_6082_);
                            lean_dec(v_k_6082_);
                            return v___x_6083_;
                        } else {
                            v_k_6084_ = lean_ctor_get(v_p_u2081_6065_, 0);
                            v_v_6085_ = lean_ctor_get(v_p_u2081_6065_, 1);
                            v_p_6086_ = lean_ctor_get(v_p_u2081_6065_, 2);
                            v_k_6087_ = lean_ctor_get(v_p_u2082_6066_, 0);
                            v_v_6088_ = lean_ctor_get(v_p_u2082_6066_, 1);
                            v_p_6089_ = lean_ctor_get(v_p_u2082_6066_, 2);
                            v_one_6090_ = lean_unsigned_to_nat(1);
                            v_n_6091_ = lean_nat_sub(v_fuel_6064_, v_one_6090_);
                            lean_dec(v_fuel_6064_);
                            v___x_6092_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_6085_, v_v_6088_);
                            match v___x_6092_ {
                                0 => {
                                    lean_inc_ref(v_p_6089_);
                                    lean_inc(v_v_6088_);
                                    lean_inc(v_k_6087_);
                                    v_isSharedCheck_6100_ =
                                        (!lean_is_exclusive(v_p_u2082_6066_)) as u8;
                                    if v_isSharedCheck_6100_ == 0 {
                                        v_unused_6101_ = lean_ctor_get(v_p_u2082_6066_, 2);
                                        lean_dec(v_unused_6101_);
                                        v_unused_6102_ = lean_ctor_get(v_p_u2082_6066_, 1);
                                        lean_dec(v_unused_6102_);
                                        v_unused_6103_ = lean_ctor_get(v_p_u2082_6066_, 0);
                                        lean_dec(v_unused_6103_);
                                        v___x_6094_ = v_p_u2082_6066_;
                                        v_isShared_6095_ = v_isSharedCheck_6100_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_p_u2082_6066_);
                                        v___x_6094_ = lean_box(0);
                                        v_isShared_6095_ = v_isSharedCheck_6100_;
                                        state = 3;
                                        continue;
                                    }
                                }
                                1 => {
                                    lean_inc_ref(v_p_6089_);
                                    lean_inc(v_k_6087_);
                                    lean_inc_ref(v_p_6086_);
                                    lean_inc(v_v_6085_);
                                    lean_inc(v_k_6084_);
                                    lean_dec_ref_known(v_p_u2081_6065_, 3);
                                    v_isSharedCheck_6115_ =
                                        (!lean_is_exclusive(v_p_u2082_6066_)) as u8;
                                    if v_isSharedCheck_6115_ == 0 {
                                        v_unused_6116_ = lean_ctor_get(v_p_u2082_6066_, 2);
                                        lean_dec(v_unused_6116_);
                                        v_unused_6117_ = lean_ctor_get(v_p_u2082_6066_, 1);
                                        lean_dec(v_unused_6117_);
                                        v_unused_6118_ = lean_ctor_get(v_p_u2082_6066_, 0);
                                        lean_dec(v_unused_6118_);
                                        v___x_6105_ = v_p_u2082_6066_;
                                        v_isShared_6106_ = v_isSharedCheck_6115_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_dec(v_p_u2082_6066_);
                                        v___x_6105_ = lean_box(0);
                                        v_isShared_6106_ = v_isSharedCheck_6115_;
                                        state = 5;
                                        continue;
                                    }
                                }
                                _ => {
                                    lean_inc_ref(v_p_6086_);
                                    lean_inc(v_v_6085_);
                                    lean_inc(v_k_6084_);
                                    v_isSharedCheck_6126_ =
                                        (!lean_is_exclusive(v_p_u2081_6065_)) as u8;
                                    if v_isSharedCheck_6126_ == 0 {
                                        v_unused_6127_ = lean_ctor_get(v_p_u2081_6065_, 2);
                                        lean_dec(v_unused_6127_);
                                        v_unused_6128_ = lean_ctor_get(v_p_u2081_6065_, 1);
                                        lean_dec(v_unused_6128_);
                                        v_unused_6129_ = lean_ctor_get(v_p_u2081_6065_, 0);
                                        lean_dec(v_unused_6129_);
                                        v___x_6120_ = v_p_u2081_6065_;
                                        v_isShared_6121_ = v_isSharedCheck_6126_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_dec(v_p_u2081_6065_);
                                        v___x_6120_ = lean_box(0);
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
                lean_dec(v_k_6071_);
                lean_dec(v_k_6070_);
                if v_isShared_6074_ == 0 {
                    lean_ctor_set(v___x_6073_, 0, v___x_6075_);
                    v___x_6077_ = v___x_6073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6075_);
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
                    lean_ctor_set(v___x_6094_, 2, v___x_6096_);
                    v___x_6098_ = v___x_6094_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6099_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6099_, 0, v_k_6087_);
                    lean_ctor_set(v_reuseFailAlloc_6099_, 1, v_v_6088_);
                    lean_ctor_set(v_reuseFailAlloc_6099_, 2, v___x_6096_);
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
                lean_dec(v_k_6087_);
                lean_dec(v_k_6084_);
                v___x_6108_ = lean_obj_once(
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
                        lean_ctor_set(v___x_6105_, 2, v___x_6110_);
                        lean_ctor_set(v___x_6105_, 1, v_v_6085_);
                        lean_ctor_set(v___x_6105_, 0, v_k_6107_);
                        v___x_6112_ = v___x_6105_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6113_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_k_6107_);
                        lean_ctor_set(v_reuseFailAlloc_6113_, 1, v_v_6085_);
                        lean_ctor_set(v_reuseFailAlloc_6113_, 2, v___x_6110_);
                        v___x_6112_ = v_reuseFailAlloc_6113_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_k_6107_);
                    lean_del_object(v___x_6105_);
                    lean_dec(v_v_6085_);
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
                    lean_ctor_set(v___x_6120_, 2, v___x_6122_);
                    v___x_6124_ = v___x_6120_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6125_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_k_6084_);
                    lean_ctor_set(v_reuseFailAlloc_6125_, 1, v_v_6085_);
                    lean_ctor_set(v_reuseFailAlloc_6125_, 2, v___x_6122_);
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
    mut v_p_u2081_6130_: *mut LeanObject,
    mut v_p_u2082_6131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    v___x_6132_ = lean_unsigned_to_nat(1000000);
    v___x_6133_ =
        l_Lean_Grind_CommRing_Poly_combine_go(v___x_6132_, v_p_u2081_6130_, v_p_u2082_6131_);
    return v___x_6133_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(
    mut v_p_u2081_6134_: *mut LeanObject,
    mut v_p_u2082_6135_: *mut LeanObject,
    mut v_h__1_6136_: *mut LeanObject,
    mut v_h__2_6137_: *mut LeanObject,
    mut v_h__3_6138_: *mut LeanObject,
    mut v_h__4_6139_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2081_6134_) == 0 {
        lean_dec(v_h__4_6139_);
        lean_dec(v_h__3_6138_);
        if lean_obj_tag(v_p_u2082_6135_) == 0 {
            let mut v_k_6140_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6141_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_6137_);
            v_k_6140_ = lean_ctor_get(v_p_u2081_6134_, 0);
            lean_inc(v_k_6140_);
            lean_dec_ref_known(v_p_u2081_6134_, 1);
            v_k_6141_ = lean_ctor_get(v_p_u2082_6135_, 0);
            lean_inc(v_k_6141_);
            lean_dec_ref_known(v_p_u2082_6135_, 1);
            v___x_6142_ = lean_apply_2(v_h__1_6136_, v_k_6140_, v_k_6141_);
            return v___x_6142_;
        } else {
            let mut v_k_6143_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6144_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6145_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_6136_);
            v_k_6143_ = lean_ctor_get(v_p_u2081_6134_, 0);
            lean_inc(v_k_6143_);
            lean_dec_ref_known(v_p_u2081_6134_, 1);
            v_k_6144_ = lean_ctor_get(v_p_u2082_6135_, 0);
            lean_inc(v_k_6144_);
            v_v_6145_ = lean_ctor_get(v_p_u2082_6135_, 1);
            lean_inc(v_v_6145_);
            v_p_6146_ = lean_ctor_get(v_p_u2082_6135_, 2);
            lean_inc_ref(v_p_6146_);
            lean_dec_ref_known(v_p_u2082_6135_, 3);
            v___x_6147_ = lean_apply_4(v_h__2_6137_, v_k_6143_, v_k_6144_, v_v_6145_, v_p_6146_);
            return v___x_6147_;
        }
    } else {
        lean_dec(v_h__2_6137_);
        lean_dec(v_h__1_6136_);
        if lean_obj_tag(v_p_u2082_6135_) == 0 {
            let mut v_k_6148_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6149_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6150_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6151_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_6139_);
            v_k_6148_ = lean_ctor_get(v_p_u2081_6134_, 0);
            lean_inc(v_k_6148_);
            v_v_6149_ = lean_ctor_get(v_p_u2081_6134_, 1);
            lean_inc(v_v_6149_);
            v_p_6150_ = lean_ctor_get(v_p_u2081_6134_, 2);
            lean_inc_ref(v_p_6150_);
            lean_dec_ref_known(v_p_u2081_6134_, 3);
            v_k_6151_ = lean_ctor_get(v_p_u2082_6135_, 0);
            lean_inc(v_k_6151_);
            lean_dec_ref_known(v_p_u2082_6135_, 1);
            v___x_6152_ = lean_apply_4(v_h__3_6138_, v_k_6148_, v_v_6149_, v_p_6150_, v_k_6151_);
            return v___x_6152_;
        } else {
            let mut v_k_6153_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6154_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6155_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6156_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6157_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6158_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_6138_);
            v_k_6153_ = lean_ctor_get(v_p_u2081_6134_, 0);
            lean_inc(v_k_6153_);
            v_v_6154_ = lean_ctor_get(v_p_u2081_6134_, 1);
            lean_inc(v_v_6154_);
            v_p_6155_ = lean_ctor_get(v_p_u2081_6134_, 2);
            lean_inc_ref(v_p_6155_);
            lean_dec_ref_known(v_p_u2081_6134_, 3);
            v_k_6156_ = lean_ctor_get(v_p_u2082_6135_, 0);
            lean_inc(v_k_6156_);
            v_v_6157_ = lean_ctor_get(v_p_u2082_6135_, 1);
            lean_inc(v_v_6157_);
            v_p_6158_ = lean_ctor_get(v_p_u2082_6135_, 2);
            lean_inc_ref(v_p_6158_);
            lean_dec_ref_known(v_p_u2082_6135_, 3);
            v___x_6159_ = lean_apply_6(
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
    mut v_motive_6160_: *mut LeanObject,
    mut v_p_u2081_6161_: *mut LeanObject,
    mut v_p_u2082_6162_: *mut LeanObject,
    mut v_h__1_6163_: *mut LeanObject,
    mut v_h__2_6164_: *mut LeanObject,
    mut v_h__3_6165_: *mut LeanObject,
    mut v_h__4_6166_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2081_6161_) == 0 {
        lean_dec(v_h__4_6166_);
        lean_dec(v_h__3_6165_);
        if lean_obj_tag(v_p_u2082_6162_) == 0 {
            let mut v_k_6167_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6168_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_6164_);
            v_k_6167_ = lean_ctor_get(v_p_u2081_6161_, 0);
            lean_inc(v_k_6167_);
            lean_dec_ref_known(v_p_u2081_6161_, 1);
            v_k_6168_ = lean_ctor_get(v_p_u2082_6162_, 0);
            lean_inc(v_k_6168_);
            lean_dec_ref_known(v_p_u2082_6162_, 1);
            v___x_6169_ = lean_apply_2(v_h__1_6163_, v_k_6167_, v_k_6168_);
            return v___x_6169_;
        } else {
            let mut v_k_6170_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6171_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6172_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_6163_);
            v_k_6170_ = lean_ctor_get(v_p_u2081_6161_, 0);
            lean_inc(v_k_6170_);
            lean_dec_ref_known(v_p_u2081_6161_, 1);
            v_k_6171_ = lean_ctor_get(v_p_u2082_6162_, 0);
            lean_inc(v_k_6171_);
            v_v_6172_ = lean_ctor_get(v_p_u2082_6162_, 1);
            lean_inc(v_v_6172_);
            v_p_6173_ = lean_ctor_get(v_p_u2082_6162_, 2);
            lean_inc_ref(v_p_6173_);
            lean_dec_ref_known(v_p_u2082_6162_, 3);
            v___x_6174_ = lean_apply_4(v_h__2_6164_, v_k_6170_, v_k_6171_, v_v_6172_, v_p_6173_);
            return v___x_6174_;
        }
    } else {
        lean_dec(v_h__2_6164_);
        lean_dec(v_h__1_6163_);
        if lean_obj_tag(v_p_u2082_6162_) == 0 {
            let mut v_k_6175_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6176_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6177_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_6166_);
            v_k_6175_ = lean_ctor_get(v_p_u2081_6161_, 0);
            lean_inc(v_k_6175_);
            v_v_6176_ = lean_ctor_get(v_p_u2081_6161_, 1);
            lean_inc(v_v_6176_);
            v_p_6177_ = lean_ctor_get(v_p_u2081_6161_, 2);
            lean_inc_ref(v_p_6177_);
            lean_dec_ref_known(v_p_u2081_6161_, 3);
            v_k_6178_ = lean_ctor_get(v_p_u2082_6162_, 0);
            lean_inc(v_k_6178_);
            lean_dec_ref_known(v_p_u2082_6162_, 1);
            v___x_6179_ = lean_apply_4(v_h__3_6165_, v_k_6175_, v_v_6176_, v_p_6177_, v_k_6178_);
            return v___x_6179_;
        } else {
            let mut v_k_6180_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6181_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6182_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6183_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_6184_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_6185_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_6165_);
            v_k_6180_ = lean_ctor_get(v_p_u2081_6161_, 0);
            lean_inc(v_k_6180_);
            v_v_6181_ = lean_ctor_get(v_p_u2081_6161_, 1);
            lean_inc(v_v_6181_);
            v_p_6182_ = lean_ctor_get(v_p_u2081_6161_, 2);
            lean_inc_ref(v_p_6182_);
            lean_dec_ref_known(v_p_u2081_6161_, 3);
            v_k_6183_ = lean_ctor_get(v_p_u2082_6162_, 0);
            lean_inc(v_k_6183_);
            v_v_6184_ = lean_ctor_get(v_p_u2082_6162_, 1);
            lean_inc(v_v_6184_);
            v_p_6185_ = lean_ctor_get(v_p_u2082_6162_, 2);
            lean_inc_ref(v_p_6185_);
            lean_dec_ref_known(v_p_u2082_6162_, 3);
            v___x_6186_ = lean_apply_6(
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
    mut v_h__1_6188_: *mut LeanObject,
    mut v_h__2_6189_: *mut LeanObject,
    mut v_h__3_6190_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_6187_ {
        0 => {
            let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_6189_);
            lean_dec(v_h__1_6188_);
            v___x_6191_ = lean_box(0);
            v___x_6192_ = lean_apply_1(v_h__3_6190_, v___x_6191_);
            return v___x_6192_;
        }
        1 => {
            let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_6190_);
            lean_dec(v_h__2_6189_);
            v___x_6193_ = lean_box(0);
            v___x_6194_ = lean_apply_1(v_h__1_6188_, v___x_6193_);
            return v___x_6194_;
        }
        _ => {
            let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_6190_);
            lean_dec(v_h__1_6188_);
            v___x_6195_ = lean_box(0);
            v___x_6196_ = lean_apply_1(v_h__2_6189_, v___x_6195_);
            return v___x_6196_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(
    mut v_x_6197_: *mut LeanObject,
    mut v_h__1_6198_: *mut LeanObject,
    mut v_h__2_6199_: *mut LeanObject,
    mut v_h__3_6200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_6201_: u8 = 0;
    let mut v_res_6202_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_6201_ = (lean_unbox(v_x_6197_) as u8);
    v_res_6202_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_36__boxed_6201_, v_h__1_6198_, v_h__2_6199_, v_h__3_6200_);
    return v_res_6202_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(
    mut v_motive_6203_: *mut LeanObject,
    mut v_x_6204_: u8,
    mut v_h__1_6205_: *mut LeanObject,
    mut v_h__2_6206_: *mut LeanObject,
    mut v_h__3_6207_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_6204_ {
        0 => {
            let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_6206_);
            lean_dec(v_h__1_6205_);
            v___x_6208_ = lean_box(0);
            v___x_6209_ = lean_apply_1(v_h__3_6207_, v___x_6208_);
            return v___x_6209_;
        }
        1 => {
            let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_6207_);
            lean_dec(v_h__2_6206_);
            v___x_6210_ = lean_box(0);
            v___x_6211_ = lean_apply_1(v_h__1_6205_, v___x_6210_);
            return v___x_6211_;
        }
        _ => {
            let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_6207_);
            lean_dec(v_h__1_6205_);
            v___x_6212_ = lean_box(0);
            v___x_6213_ = lean_apply_1(v_h__2_6206_, v___x_6212_);
            return v___x_6213_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(
    mut v_motive_6214_: *mut LeanObject,
    mut v_x_6215_: *mut LeanObject,
    mut v_h__1_6216_: *mut LeanObject,
    mut v_h__2_6217_: *mut LeanObject,
    mut v_h__3_6218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_6219_: u8 = 0;
    let mut v_res_6220_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_6219_ = (lean_unbox(v_x_6215_) as u8);
    v_res_6220_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_6214_, v_x_51__boxed_6219_, v_h__1_6216_, v_h__2_6217_, v_h__3_6218_);
    return v_res_6220_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mul_go(
    mut v_p_u2082_6221_: *mut LeanObject,
    mut v_p_u2081_6222_: *mut LeanObject,
    mut v_acc_6223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_6222_) == 0 {
                    v_k_6224_ = lean_ctor_get(v_p_u2081_6222_, 0);
                    lean_inc(v_k_6224_);
                    lean_dec_ref_known(v_p_u2081_6222_, 1);
                    v___x_6225_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6224_, v_p_u2082_6221_);
                    lean_dec(v_k_6224_);
                    v___x_6226_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_6223_, v___x_6225_);
                    return v___x_6226_;
                } else {
                    v_k_6227_ = lean_ctor_get(v_p_u2081_6222_, 0);
                    lean_inc(v_k_6227_);
                    v_v_6228_ = lean_ctor_get(v_p_u2081_6222_, 1);
                    lean_inc(v_v_6228_);
                    v_p_6229_ = lean_ctor_get(v_p_u2081_6222_, 2);
                    lean_inc_ref(v_p_6229_);
                    lean_dec_ref_known(v_p_u2081_6222_, 3);
                    lean_inc_ref(v_p_u2082_6221_);
                    v___x_6230_ =
                        l_Lean_Grind_CommRing_Poly_mulMon(v_k_6227_, v_v_6228_, v_p_u2082_6221_);
                    lean_dec(v_k_6227_);
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
    mut v_p_u2081_6233_: *mut LeanObject,
    mut v_p_u2082_6234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    v___x_6235_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6236_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_6234_, v_p_u2081_6233_, v___x_6235_);
    return v___x_6236_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mul__nc_go(
    mut v_p_u2082_6237_: *mut LeanObject,
    mut v_p_u2081_6238_: *mut LeanObject,
    mut v_acc_6239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_6238_) == 0 {
                    v_k_6240_ = lean_ctor_get(v_p_u2081_6238_, 0);
                    lean_inc(v_k_6240_);
                    lean_dec_ref_known(v_p_u2081_6238_, 1);
                    v___x_6241_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_6240_, v_p_u2082_6237_);
                    lean_dec(v_k_6240_);
                    v___x_6242_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_6239_, v___x_6241_);
                    return v___x_6242_;
                } else {
                    v_k_6243_ = lean_ctor_get(v_p_u2081_6238_, 0);
                    lean_inc(v_k_6243_);
                    v_v_6244_ = lean_ctor_get(v_p_u2081_6238_, 1);
                    lean_inc(v_v_6244_);
                    v_p_6245_ = lean_ctor_get(v_p_u2081_6238_, 2);
                    lean_inc_ref(v_p_6245_);
                    lean_dec_ref_known(v_p_u2081_6238_, 3);
                    lean_inc_ref(v_p_u2082_6237_);
                    v___x_6246_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(
                        v_k_6243_,
                        v_v_6244_,
                        v_p_u2082_6237_,
                    );
                    lean_dec(v_k_6243_);
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
    mut v_p_u2081_6249_: *mut LeanObject,
    mut v_p_u2082_6250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    v___x_6251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6252_ =
        l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_6250_, v_p_u2081_6249_, v___x_6251_);
    return v___x_6252_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_pow___closed__0() -> *mut LeanObject {
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    v___x_6253_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_6254_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6254_, 0, v___x_6253_);
    return v___x_6254_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow(
    mut v_p_6255_: *mut LeanObject,
    mut v_k_6256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6258_: u8 = 0;
    v_zero_6257_ = lean_unsigned_to_nat(0);
    v_isZero_6258_ = lean_nat_dec_eq(v_k_6256_, v_zero_6257_);
    if v_isZero_6258_ == 1 {
        let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_6255_);
        v___x_6259_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6259_;
    } else {
        let mut v_one_6260_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_6261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6262_: u8 = 0;
        v_one_6260_ = lean_unsigned_to_nat(1);
        v_n_6261_ = lean_nat_sub(v_k_6256_, v_one_6260_);
        v___x_6262_ = lean_nat_dec_eq(v_n_6261_, v_zero_6257_);
        if v___x_6262_ == 0 {
            let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_p_6255_);
            v___x_6263_ = l_Lean_Grind_CommRing_Poly_pow(v_p_6255_, v_n_6261_);
            lean_dec(v_n_6261_);
            v___x_6264_ = l_Lean_Grind_CommRing_Poly_mul(v_p_6255_, v___x_6263_);
            return v___x_6264_;
        } else {
            lean_dec(v_n_6261_);
            return v_p_6255_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow___boxed(
    mut v_p_6265_: *mut LeanObject,
    mut v_k_6266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6267_: *mut LeanObject = core::ptr::null_mut();
    v_res_6267_ = l_Lean_Grind_CommRing_Poly_pow(v_p_6265_, v_k_6266_);
    lean_dec(v_k_6266_);
    return v_res_6267_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow__nc(
    mut v_p_6268_: *mut LeanObject,
    mut v_k_6269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6271_: u8 = 0;
    v_zero_6270_ = lean_unsigned_to_nat(0);
    v_isZero_6271_ = lean_nat_dec_eq(v_k_6269_, v_zero_6270_);
    if v_isZero_6271_ == 1 {
        let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_6268_);
        v___x_6272_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6272_;
    } else {
        let mut v_one_6273_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_6274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6275_: u8 = 0;
        v_one_6273_ = lean_unsigned_to_nat(1);
        v_n_6274_ = lean_nat_sub(v_k_6269_, v_one_6273_);
        v___x_6275_ = lean_nat_dec_eq(v_n_6274_, v_zero_6270_);
        if v___x_6275_ == 0 {
            let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_p_6268_);
            v___x_6276_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_6268_, v_n_6274_);
            lean_dec(v_n_6274_);
            v___x_6277_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_6276_, v_p_6268_);
            return v___x_6277_;
        } else {
            lean_dec(v_n_6274_);
            return v_p_6268_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_pow__nc___boxed(
    mut v_p_6278_: *mut LeanObject,
    mut v_k_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6280_: *mut LeanObject = core::ptr::null_mut();
    v_res_6280_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_6278_, v_k_6279_);
    lean_dec(v_k_6279_);
    return v_res_6280_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0() -> *mut LeanObject {
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    v___x_6281_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
        _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
    );
    v___x_6282_ = lean_int_neg(v___x_6281_);
    return v___x_6282_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPoly(mut v_x_6283_: *mut LeanObject) -> *mut LeanObject {
    let mut v_k_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6291_: u8 = 0;
    let mut v_k_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut v_k_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6304_: u8 = 0;
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6308_: u8 = 0;
    let mut v_i_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v_n_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: u8 = 0;
    let mut v_k_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6348_: u8 = 0;
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6354_: u8 = 0;
    let mut v_i_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_6283_) {
                0 => {
                    v_k_6284_ = lean_ctor_get(v_x_6283_, 0);
                    v_isSharedCheck_6291_ = (!lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6291_ == 0 {
                        v___x_6286_ = v_x_6283_;
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_6284_);
                        lean_dec(v_x_6283_);
                        v___x_6286_ = lean_box(0);
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_6292_ = lean_ctor_get(v_x_6283_, 0);
                    v_isSharedCheck_6300_ = (!lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6300_ == 0 {
                        v___x_6294_ = v_x_6283_;
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_k_6292_);
                        lean_dec(v_x_6283_);
                        v___x_6294_ = lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_k_6301_ = lean_ctor_get(v_x_6283_, 0);
                    v_isSharedCheck_6308_ = (!lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6308_ == 0 {
                        v___x_6303_ = v_x_6283_;
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_k_6301_);
                        lean_dec(v_x_6283_);
                        v___x_6303_ = lean_box(0);
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_6309_ = lean_ctor_get(v_x_6283_, 0);
                    lean_inc(v_i_6309_);
                    lean_dec_ref_known(v_x_6283_, 1);
                    v___x_6310_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_6309_);
                    return v___x_6310_;
                }
                4 => {
                    v_a_6311_ = lean_ctor_get(v_x_6283_, 0);
                    lean_inc_ref(v_a_6311_);
                    lean_dec_ref_known(v_x_6283_, 1);
                    v___x_6312_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_6313_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6311_);
                    v___x_6314_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_6312_, v___x_6313_);
                    return v___x_6314_;
                }
                5 => {
                    v_a_6315_ = lean_ctor_get(v_x_6283_, 0);
                    lean_inc_ref(v_a_6315_);
                    v_b_6316_ = lean_ctor_get(v_x_6283_, 1);
                    lean_inc_ref(v_b_6316_);
                    lean_dec_ref_known(v_x_6283_, 2);
                    v___x_6317_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6315_);
                    v___x_6318_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_6316_);
                    v___x_6319_ = l_Lean_Grind_CommRing_Poly_combine(v___x_6317_, v___x_6318_);
                    return v___x_6319_;
                }
                6 => {
                    v_a_6320_ = lean_ctor_get(v_x_6283_, 0);
                    lean_inc_ref(v_a_6320_);
                    v_b_6321_ = lean_ctor_get(v_x_6283_, 1);
                    lean_inc_ref(v_b_6321_);
                    lean_dec_ref_known(v_x_6283_, 2);
                    v___x_6322_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6320_);
                    v___x_6323_ = lean_obj_once(
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
                    v_a_6327_ = lean_ctor_get(v_x_6283_, 0);
                    lean_inc_ref(v_a_6327_);
                    v_b_6328_ = lean_ctor_get(v_x_6283_, 1);
                    lean_inc_ref(v_b_6328_);
                    lean_dec_ref_known(v_x_6283_, 2);
                    v___x_6329_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6327_);
                    v___x_6330_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_6328_);
                    v___x_6331_ = l_Lean_Grind_CommRing_Poly_mul(v___x_6329_, v___x_6330_);
                    return v___x_6331_;
                }
                _ => {
                    v_a_6332_ = lean_ctor_get(v_x_6283_, 0);
                    v_k_6333_ = lean_ctor_get(v_x_6283_, 1);
                    v_isSharedCheck_6365_ = (!lean_is_exclusive(v_x_6283_)) as u8;
                    if v_isSharedCheck_6365_ == 0 {
                        v___x_6335_ = v_x_6283_;
                        v_isShared_6336_ = v_isSharedCheck_6365_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_k_6333_);
                        lean_inc(v_a_6332_);
                        lean_dec(v_x_6283_);
                        v___x_6335_ = lean_box(0);
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
                    v_reuseFailAlloc_6290_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_k_6284_);
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
                    lean_ctor_set_tag(v___x_6294_, 0);
                    lean_ctor_set(v___x_6294_, 0, v___x_6296_);
                    v___x_6298_ = v___x_6294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6299_, 0, v___x_6296_);
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
                    lean_ctor_set_tag(v___x_6303_, 0);
                    v___x_6306_ = v___x_6303_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6307_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6307_, 0, v_k_6301_);
                    v___x_6306_ = v_reuseFailAlloc_6307_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6306_;
            }
            7 => {
                v___x_6341_ = lean_unsigned_to_nat(0);
                v___x_6342_ = lean_nat_dec_eq(v_k_6333_, v___x_6341_);
                if v___x_6342_ == 0 {
                    match lean_obj_tag(v_a_6332_) {
                        0 => {
                            lean_del_object(v___x_6335_);
                            v_k_6343_ = lean_ctor_get(v_a_6332_, 0);
                            lean_inc(v_k_6343_);
                            lean_dec_ref_known(v_a_6332_, 1);
                            v_n_6338_ = v_k_6343_;
                            state = 8;
                            continue;
                        }
                        2 => {
                            lean_del_object(v___x_6335_);
                            v_k_6344_ = lean_ctor_get(v_a_6332_, 0);
                            lean_inc(v_k_6344_);
                            lean_dec_ref_known(v_a_6332_, 1);
                            v_n_6338_ = v_k_6344_;
                            state = 8;
                            continue;
                        }
                        1 => {
                            lean_del_object(v___x_6335_);
                            v_k_6345_ = lean_ctor_get(v_a_6332_, 0);
                            v_isSharedCheck_6354_ = (!lean_is_exclusive(v_a_6332_)) as u8;
                            if v_isSharedCheck_6354_ == 0 {
                                v___x_6347_ = v_a_6332_;
                                v_isShared_6348_ = v_isSharedCheck_6354_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_k_6345_);
                                lean_dec(v_a_6332_);
                                v___x_6347_ = lean_box(0);
                                v_isShared_6348_ = v_isSharedCheck_6354_;
                                state = 9;
                                continue;
                            }
                        }
                        3 => {
                            v_i_6355_ = lean_ctor_get(v_a_6332_, 0);
                            lean_inc(v_i_6355_);
                            lean_dec_ref_known(v_a_6332_, 1);
                            if v_isShared_6336_ == 0 {
                                lean_ctor_set_tag(v___x_6335_, 0);
                                lean_ctor_set(v___x_6335_, 0, v_i_6355_);
                                v___x_6357_ = v___x_6335_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_6361_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_i_6355_);
                                lean_ctor_set(v_reuseFailAlloc_6361_, 1, v_k_6333_);
                                v___x_6357_ = v_reuseFailAlloc_6361_;
                                state = 11;
                                continue;
                            }
                        }
                        _ => {
                            lean_del_object(v___x_6335_);
                            v___x_6362_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_6332_);
                            v___x_6363_ = l_Lean_Grind_CommRing_Poly_pow(v___x_6362_, v_k_6333_);
                            lean_dec(v_k_6333_);
                            return v___x_6363_;
                        }
                    }
                } else {
                    lean_del_object(v___x_6335_);
                    lean_dec(v_k_6333_);
                    lean_dec_ref(v_a_6332_);
                    v___x_6364_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_6364_;
                }
            }
            8 => {
                v___x_6339_ = l_Int_pow(v_n_6338_, v_k_6333_);
                lean_dec(v_k_6333_);
                lean_dec(v_n_6338_);
                v___x_6340_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6340_, 0, v___x_6339_);
                return v___x_6340_;
            }
            9 => {
                v___x_6349_ = lean_nat_to_int(v_k_6345_);
                v___x_6350_ = l_Int_pow(v___x_6349_, v_k_6333_);
                lean_dec(v_k_6333_);
                lean_dec(v___x_6349_);
                if v_isShared_6348_ == 0 {
                    lean_ctor_set_tag(v___x_6347_, 0);
                    lean_ctor_set(v___x_6347_, 0, v___x_6350_);
                    v___x_6352_ = v___x_6347_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6353_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6350_);
                    v___x_6352_ = v_reuseFailAlloc_6353_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6352_;
            }
            11 => {
                v___x_6358_ = lean_box(0);
                v___x_6359_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6359_, 0, v___x_6357_);
                lean_ctor_set(v___x_6359_, 1, v___x_6358_);
                v___x_6360_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_6359_);
                return v___x_6360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degreeOf(
    mut v_m_6366_: *mut LeanObject,
    mut v_x_6367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_6366_) == 0 {
                    v___x_6368_ = lean_unsigned_to_nat(0);
                    return v___x_6368_;
                } else {
                    v_p_6369_ = lean_ctor_get(v_m_6366_, 0);
                    v_m_6370_ = lean_ctor_get(v_m_6366_, 1);
                    v_x_6371_ = lean_ctor_get(v_p_6369_, 0);
                    v_k_6372_ = lean_ctor_get(v_p_6369_, 1);
                    v___x_6373_ = lean_nat_dec_eq(v_x_6371_, v_x_6367_);
                    if v___x_6373_ == 0 {
                        v_m_6366_ = v_m_6370_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_k_6372_);
                        return v_k_6372_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_degreeOf___boxed(
    mut v_m_6375_: *mut LeanObject,
    mut v_x_6376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6377_: *mut LeanObject = core::ptr::null_mut();
    v_res_6377_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_6375_, v_x_6376_);
    lean_dec(v_x_6376_);
    lean_dec(v_m_6375_);
    return v_res_6377_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_cancelVar(
    mut v_m_6378_: *mut LeanObject,
    mut v_x_6379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6384_: u8 = 0;
    let mut v_x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: u8 = 0;
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_6378_) == 0 {
                    return v_m_6378_;
                } else {
                    v_p_6380_ = lean_ctor_get(v_m_6378_, 0);
                    v_m_6381_ = lean_ctor_get(v_m_6378_, 1);
                    v_isSharedCheck_6391_ = (!lean_is_exclusive(v_m_6378_)) as u8;
                    if v_isSharedCheck_6391_ == 0 {
                        v___x_6383_ = v_m_6378_;
                        v_isShared_6384_ = v_isSharedCheck_6391_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_m_6381_);
                        lean_inc(v_p_6380_);
                        lean_dec(v_m_6378_);
                        v___x_6383_ = lean_box(0);
                        v_isShared_6384_ = v_isSharedCheck_6391_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_x_6385_ = lean_ctor_get(v_p_6380_, 0);
                v___x_6386_ = lean_nat_dec_eq(v_x_6385_, v_x_6379_);
                if v___x_6386_ == 0 {
                    v___x_6387_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_6381_, v_x_6379_);
                    if v_isShared_6384_ == 0 {
                        lean_ctor_set(v___x_6383_, 1, v___x_6387_);
                        v___x_6389_ = v___x_6383_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6390_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_p_6380_);
                        lean_ctor_set(v_reuseFailAlloc_6390_, 1, v___x_6387_);
                        v___x_6389_ = v_reuseFailAlloc_6390_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6383_);
                    lean_dec_ref(v_p_6380_);
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
    mut v_m_6392_: *mut LeanObject,
    mut v_x_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6394_: *mut LeanObject = core::ptr::null_mut();
    v_res_6394_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_6392_, v_x_6393_);
    lean_dec(v_x_6393_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar_x27(
    mut v_c_6395_: *mut LeanObject,
    mut v_x_6396_: *mut LeanObject,
    mut v_p_6397_: *mut LeanObject,
    mut v_acc_6398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6406_: u8 = 0;
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: u8 = 0;
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_6397_) == 0 {
                    v_k_6399_ = lean_ctor_get(v_p_6397_, 0);
                    lean_inc(v_k_6399_);
                    lean_dec_ref_known(v_p_6397_, 1);
                    v___x_6400_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_6398_, v_k_6399_);
                    lean_dec(v_k_6399_);
                    return v___x_6400_;
                } else {
                    v_k_6401_ = lean_ctor_get(v_p_6397_, 0);
                    lean_inc(v_k_6401_);
                    v_v_6402_ = lean_ctor_get(v_p_6397_, 1);
                    lean_inc(v_v_6402_);
                    v_p_6403_ = lean_ctor_get(v_p_6397_, 2);
                    lean_inc_ref(v_p_6403_);
                    lean_dec_ref_known(v_p_6397_, 3);
                    v_n_6404_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_6402_, v_x_6396_);
                    v___x_6414_ = lean_unsigned_to_nat(0);
                    v___x_6415_ = lean_nat_dec_lt(v___x_6414_, v_n_6404_);
                    if v___x_6415_ == 0 {
                        v___y_6406_ = v___x_6415_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6416_ = l_Int_pow(v_c_6395_, v_n_6404_);
                        v___x_6417_ = l_Int_decidableDvd(v___x_6416_, v_k_6401_);
                        lean_dec(v___x_6416_);
                        v___y_6406_ = v___x_6417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6406_ == 0 {
                    lean_dec(v_n_6404_);
                    v___x_6407_ =
                        l_Lean_Grind_CommRing_Poly_insert(v_k_6401_, v_v_6402_, v_acc_6398_);
                    v_p_6397_ = v_p_6403_;
                    v_acc_6398_ = v___x_6407_;
                    state = 0;
                    continue;
                } else {
                    v___x_6409_ = l_Int_pow(v_c_6395_, v_n_6404_);
                    lean_dec(v_n_6404_);
                    v___x_6410_ = lean_int_ediv(v_k_6401_, v___x_6409_);
                    lean_dec(v___x_6409_);
                    lean_dec(v_k_6401_);
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
    mut v_c_6418_: *mut LeanObject,
    mut v_x_6419_: *mut LeanObject,
    mut v_p_6420_: *mut LeanObject,
    mut v_acc_6421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6422_: *mut LeanObject = core::ptr::null_mut();
    v_res_6422_ =
        l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_6418_, v_x_6419_, v_p_6420_, v_acc_6421_);
    lean_dec(v_x_6419_);
    lean_dec(v_c_6418_);
    return v_res_6422_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar(
    mut v_c_6423_: *mut LeanObject,
    mut v_x_6424_: *mut LeanObject,
    mut v_p_6425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    v___x_6426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
    );
    v___x_6427_ =
        l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_6423_, v_x_6424_, v_p_6425_, v___x_6426_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_cancelVar___boxed(
    mut v_c_6428_: *mut LeanObject,
    mut v_x_6429_: *mut LeanObject,
    mut v_p_6430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6431_: *mut LeanObject = core::ptr::null_mut();
    v_res_6431_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_6428_, v_x_6429_, v_p_6430_);
    lean_dec(v_x_6429_);
    lean_dec(v_c_6428_);
    return v_res_6431_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(
    mut v_x_6432_: *mut LeanObject,
    mut v_h__1_6433_: *mut LeanObject,
    mut v_h__2_6434_: *mut LeanObject,
    mut v_h__3_6435_: *mut LeanObject,
    mut v_h__4_6436_: *mut LeanObject,
    mut v_h__5_6437_: *mut LeanObject,
    mut v_h__6_6438_: *mut LeanObject,
    mut v_h__7_6439_: *mut LeanObject,
    mut v_h__8_6440_: *mut LeanObject,
    mut v_h__9_6441_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_6432_) {
        0 => {
            let mut v_k_6442_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            v_k_6442_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc(v_k_6442_);
            lean_dec_ref_known(v_x_6432_, 1);
            v___x_6443_ = lean_apply_1(v_h__1_6433_, v_k_6442_);
            return v___x_6443_;
        }
        1 => {
            let mut v_k_6444_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_k_6444_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc(v_k_6444_);
            lean_dec_ref_known(v_x_6432_, 1);
            v___x_6445_ = lean_apply_1(v_h__3_6435_, v_k_6444_);
            return v___x_6445_;
        }
        2 => {
            let mut v_k_6446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__1_6433_);
            v_k_6446_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc(v_k_6446_);
            lean_dec_ref_known(v_x_6432_, 1);
            v___x_6447_ = lean_apply_1(v_h__2_6434_, v_k_6446_);
            return v___x_6447_;
        }
        3 => {
            let mut v_i_6448_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_i_6448_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc(v_i_6448_);
            lean_dec_ref_known(v_x_6432_, 1);
            v___x_6449_ = lean_apply_1(v_h__4_6436_, v_i_6448_);
            return v___x_6449_;
        }
        4 => {
            let mut v_a_6450_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_a_6450_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc_ref(v_a_6450_);
            lean_dec_ref_known(v_x_6432_, 1);
            v___x_6451_ = lean_apply_1(v_h__7_6439_, v_a_6450_);
            return v___x_6451_;
        }
        5 => {
            let mut v_a_6452_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_6453_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_a_6452_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc_ref(v_a_6452_);
            v_b_6453_ = lean_ctor_get(v_x_6432_, 1);
            lean_inc_ref(v_b_6453_);
            lean_dec_ref_known(v_x_6432_, 2);
            v___x_6454_ = lean_apply_2(v_h__5_6437_, v_a_6452_, v_b_6453_);
            return v___x_6454_;
        }
        6 => {
            let mut v_a_6455_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_6456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_a_6455_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc_ref(v_a_6455_);
            v_b_6456_ = lean_ctor_get(v_x_6432_, 1);
            lean_inc_ref(v_b_6456_);
            lean_dec_ref_known(v_x_6432_, 2);
            v___x_6457_ = lean_apply_2(v_h__8_6440_, v_a_6455_, v_b_6456_);
            return v___x_6457_;
        }
        7 => {
            let mut v_a_6458_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_6459_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6441_);
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_a_6458_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc_ref(v_a_6458_);
            v_b_6459_ = lean_ctor_get(v_x_6432_, 1);
            lean_inc_ref(v_b_6459_);
            lean_dec_ref_known(v_x_6432_, 2);
            v___x_6460_ = lean_apply_2(v_h__6_6438_, v_a_6458_, v_b_6459_);
            return v___x_6460_;
        }
        _ => {
            let mut v_a_6461_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6462_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_6440_);
            lean_dec(v_h__7_6439_);
            lean_dec(v_h__6_6438_);
            lean_dec(v_h__5_6437_);
            lean_dec(v_h__4_6436_);
            lean_dec(v_h__3_6435_);
            lean_dec(v_h__2_6434_);
            lean_dec(v_h__1_6433_);
            v_a_6461_ = lean_ctor_get(v_x_6432_, 0);
            lean_inc_ref(v_a_6461_);
            v_k_6462_ = lean_ctor_get(v_x_6432_, 1);
            lean_inc(v_k_6462_);
            lean_dec_ref_known(v_x_6432_, 2);
            v___x_6463_ = lean_apply_2(v_h__9_6441_, v_a_6461_, v_k_6462_);
            return v___x_6463_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(
    mut v_motive_6464_: *mut LeanObject,
    mut v_x_6465_: *mut LeanObject,
    mut v_h__1_6466_: *mut LeanObject,
    mut v_h__2_6467_: *mut LeanObject,
    mut v_h__3_6468_: *mut LeanObject,
    mut v_h__4_6469_: *mut LeanObject,
    mut v_h__5_6470_: *mut LeanObject,
    mut v_h__6_6471_: *mut LeanObject,
    mut v_h__7_6472_: *mut LeanObject,
    mut v_h__8_6473_: *mut LeanObject,
    mut v_h__9_6474_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_6465_) {
        0 => {
            let mut v_k_6475_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            v_k_6475_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc(v_k_6475_);
            lean_dec_ref_known(v_x_6465_, 1);
            v___x_6476_ = lean_apply_1(v_h__1_6466_, v_k_6475_);
            return v___x_6476_;
        }
        1 => {
            let mut v_k_6477_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_k_6477_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc(v_k_6477_);
            lean_dec_ref_known(v_x_6465_, 1);
            v___x_6478_ = lean_apply_1(v_h__3_6468_, v_k_6477_);
            return v___x_6478_;
        }
        2 => {
            let mut v_k_6479_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__1_6466_);
            v_k_6479_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc(v_k_6479_);
            lean_dec_ref_known(v_x_6465_, 1);
            v___x_6480_ = lean_apply_1(v_h__2_6467_, v_k_6479_);
            return v___x_6480_;
        }
        3 => {
            let mut v_i_6481_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_i_6481_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc(v_i_6481_);
            lean_dec_ref_known(v_x_6465_, 1);
            v___x_6482_ = lean_apply_1(v_h__4_6469_, v_i_6481_);
            return v___x_6482_;
        }
        4 => {
            let mut v_a_6483_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_a_6483_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc_ref(v_a_6483_);
            lean_dec_ref_known(v_x_6465_, 1);
            v___x_6484_ = lean_apply_1(v_h__7_6472_, v_a_6483_);
            return v___x_6484_;
        }
        5 => {
            let mut v_a_6485_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_6486_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_a_6485_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc_ref(v_a_6485_);
            v_b_6486_ = lean_ctor_get(v_x_6465_, 1);
            lean_inc_ref(v_b_6486_);
            lean_dec_ref_known(v_x_6465_, 2);
            v___x_6487_ = lean_apply_2(v_h__5_6470_, v_a_6485_, v_b_6486_);
            return v___x_6487_;
        }
        6 => {
            let mut v_a_6488_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_6489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_a_6488_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc_ref(v_a_6488_);
            v_b_6489_ = lean_ctor_get(v_x_6465_, 1);
            lean_inc_ref(v_b_6489_);
            lean_dec_ref_known(v_x_6465_, 2);
            v___x_6490_ = lean_apply_2(v_h__8_6473_, v_a_6488_, v_b_6489_);
            return v___x_6490_;
        }
        7 => {
            let mut v_a_6491_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_6492_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_6474_);
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_a_6491_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc_ref(v_a_6491_);
            v_b_6492_ = lean_ctor_get(v_x_6465_, 1);
            lean_inc_ref(v_b_6492_);
            lean_dec_ref_known(v_x_6465_, 2);
            v___x_6493_ = lean_apply_2(v_h__6_6471_, v_a_6491_, v_b_6492_);
            return v___x_6493_;
        }
        _ => {
            let mut v_a_6494_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_6495_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_6473_);
            lean_dec(v_h__7_6472_);
            lean_dec(v_h__6_6471_);
            lean_dec(v_h__5_6470_);
            lean_dec(v_h__4_6469_);
            lean_dec(v_h__3_6468_);
            lean_dec(v_h__2_6467_);
            lean_dec(v_h__1_6466_);
            v_a_6494_ = lean_ctor_get(v_x_6465_, 0);
            lean_inc_ref(v_a_6494_);
            v_k_6495_ = lean_ctor_get(v_x_6465_, 1);
            lean_inc(v_k_6495_);
            lean_dec_ref_known(v_x_6465_, 2);
            v___x_6496_ = lean_apply_2(v_h__9_6474_, v_a_6494_, v_k_6495_);
            return v___x_6496_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(
    mut v_a_6497_: *mut LeanObject,
    mut v_h__1_6498_: *mut LeanObject,
    mut v_h__2_6499_: *mut LeanObject,
    mut v_h__3_6500_: *mut LeanObject,
    mut v_h__4_6501_: *mut LeanObject,
    mut v_h__5_6502_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_6497_) {
        0 => {
            let mut v_k_6503_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6502_);
            lean_dec(v_h__4_6501_);
            lean_dec(v_h__3_6500_);
            lean_dec(v_h__2_6499_);
            v_k_6503_ = lean_ctor_get(v_a_6497_, 0);
            lean_inc(v_k_6503_);
            lean_dec_ref_known(v_a_6497_, 1);
            v___x_6504_ = lean_apply_1(v_h__1_6498_, v_k_6503_);
            return v___x_6504_;
        }
        2 => {
            let mut v_k_6505_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6502_);
            lean_dec(v_h__4_6501_);
            lean_dec(v_h__3_6500_);
            lean_dec(v_h__1_6498_);
            v_k_6505_ = lean_ctor_get(v_a_6497_, 0);
            lean_inc(v_k_6505_);
            lean_dec_ref_known(v_a_6497_, 1);
            v___x_6506_ = lean_apply_1(v_h__2_6499_, v_k_6505_);
            return v___x_6506_;
        }
        1 => {
            let mut v_k_6507_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6502_);
            lean_dec(v_h__4_6501_);
            lean_dec(v_h__2_6499_);
            lean_dec(v_h__1_6498_);
            v_k_6507_ = lean_ctor_get(v_a_6497_, 0);
            lean_inc(v_k_6507_);
            lean_dec_ref_known(v_a_6497_, 1);
            v___x_6508_ = lean_apply_1(v_h__3_6500_, v_k_6507_);
            return v___x_6508_;
        }
        3 => {
            let mut v_i_6509_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6502_);
            lean_dec(v_h__3_6500_);
            lean_dec(v_h__2_6499_);
            lean_dec(v_h__1_6498_);
            v_i_6509_ = lean_ctor_get(v_a_6497_, 0);
            lean_inc(v_i_6509_);
            lean_dec_ref_known(v_a_6497_, 1);
            v___x_6510_ = lean_apply_1(v_h__4_6501_, v_i_6509_);
            return v___x_6510_;
        }
        _ => {
            let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_6501_);
            lean_dec(v_h__3_6500_);
            lean_dec(v_h__2_6499_);
            lean_dec(v_h__1_6498_);
            v___x_6511_ = lean_apply_5(
                v_h__5_6502_,
                v_a_6497_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_6511_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(
    mut v_motive_6512_: *mut LeanObject,
    mut v_a_6513_: *mut LeanObject,
    mut v_h__1_6514_: *mut LeanObject,
    mut v_h__2_6515_: *mut LeanObject,
    mut v_h__3_6516_: *mut LeanObject,
    mut v_h__4_6517_: *mut LeanObject,
    mut v_h__5_6518_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_6513_) {
        0 => {
            let mut v_k_6519_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6518_);
            lean_dec(v_h__4_6517_);
            lean_dec(v_h__3_6516_);
            lean_dec(v_h__2_6515_);
            v_k_6519_ = lean_ctor_get(v_a_6513_, 0);
            lean_inc(v_k_6519_);
            lean_dec_ref_known(v_a_6513_, 1);
            v___x_6520_ = lean_apply_1(v_h__1_6514_, v_k_6519_);
            return v___x_6520_;
        }
        2 => {
            let mut v_k_6521_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6518_);
            lean_dec(v_h__4_6517_);
            lean_dec(v_h__3_6516_);
            lean_dec(v_h__1_6514_);
            v_k_6521_ = lean_ctor_get(v_a_6513_, 0);
            lean_inc(v_k_6521_);
            lean_dec_ref_known(v_a_6513_, 1);
            v___x_6522_ = lean_apply_1(v_h__2_6515_, v_k_6521_);
            return v___x_6522_;
        }
        1 => {
            let mut v_k_6523_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6518_);
            lean_dec(v_h__4_6517_);
            lean_dec(v_h__2_6515_);
            lean_dec(v_h__1_6514_);
            v_k_6523_ = lean_ctor_get(v_a_6513_, 0);
            lean_inc(v_k_6523_);
            lean_dec_ref_known(v_a_6513_, 1);
            v___x_6524_ = lean_apply_1(v_h__3_6516_, v_k_6523_);
            return v___x_6524_;
        }
        3 => {
            let mut v_i_6525_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_6518_);
            lean_dec(v_h__3_6516_);
            lean_dec(v_h__2_6515_);
            lean_dec(v_h__1_6514_);
            v_i_6525_ = lean_ctor_get(v_a_6513_, 0);
            lean_inc(v_i_6525_);
            lean_dec_ref_known(v_a_6513_, 1);
            v___x_6526_ = lean_apply_1(v_h__4_6517_, v_i_6525_);
            return v___x_6526_;
        }
        _ => {
            let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_6517_);
            lean_dec(v_h__3_6516_);
            lean_dec(v_h__2_6515_);
            lean_dec(v_h__1_6514_);
            v___x_6527_ = lean_apply_5(
                v_h__5_6518_,
                v_a_6513_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_6527_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPoly__nc(
    mut v_x_6528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut v_k_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6540_: u8 = 0;
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6545_: u8 = 0;
    let mut v_k_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6549_: u8 = 0;
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6553_: u8 = 0;
    let mut v_i_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6581_: u8 = 0;
    let mut v_n_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: u8 = 0;
    let mut v_k_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6593_: u8 = 0;
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_i_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_6528_) {
                0 => {
                    v_k_6529_ = lean_ctor_get(v_x_6528_, 0);
                    v_isSharedCheck_6536_ = (!lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6536_ == 0 {
                        v___x_6531_ = v_x_6528_;
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_6529_);
                        lean_dec(v_x_6528_);
                        v___x_6531_ = lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_6537_ = lean_ctor_get(v_x_6528_, 0);
                    v_isSharedCheck_6545_ = (!lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6545_ == 0 {
                        v___x_6539_ = v_x_6528_;
                        v_isShared_6540_ = v_isSharedCheck_6545_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_k_6537_);
                        lean_dec(v_x_6528_);
                        v___x_6539_ = lean_box(0);
                        v_isShared_6540_ = v_isSharedCheck_6545_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_k_6546_ = lean_ctor_get(v_x_6528_, 0);
                    v_isSharedCheck_6553_ = (!lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6553_ == 0 {
                        v___x_6548_ = v_x_6528_;
                        v_isShared_6549_ = v_isSharedCheck_6553_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_k_6546_);
                        lean_dec(v_x_6528_);
                        v___x_6548_ = lean_box(0);
                        v_isShared_6549_ = v_isSharedCheck_6553_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_6554_ = lean_ctor_get(v_x_6528_, 0);
                    lean_inc(v_i_6554_);
                    lean_dec_ref_known(v_x_6528_, 1);
                    v___x_6555_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_6554_);
                    return v___x_6555_;
                }
                4 => {
                    v_a_6556_ = lean_ctor_get(v_x_6528_, 0);
                    lean_inc_ref(v_a_6556_);
                    lean_dec_ref_known(v_x_6528_, 1);
                    v___x_6557_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    v___x_6558_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6556_);
                    v___x_6559_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_6557_, v___x_6558_);
                    return v___x_6559_;
                }
                5 => {
                    v_a_6560_ = lean_ctor_get(v_x_6528_, 0);
                    lean_inc_ref(v_a_6560_);
                    v_b_6561_ = lean_ctor_get(v_x_6528_, 1);
                    lean_inc_ref(v_b_6561_);
                    lean_dec_ref_known(v_x_6528_, 2);
                    v___x_6562_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6560_);
                    v___x_6563_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_6561_);
                    v___x_6564_ = l_Lean_Grind_CommRing_Poly_combine(v___x_6562_, v___x_6563_);
                    return v___x_6564_;
                }
                6 => {
                    v_a_6565_ = lean_ctor_get(v_x_6528_, 0);
                    lean_inc_ref(v_a_6565_);
                    v_b_6566_ = lean_ctor_get(v_x_6528_, 1);
                    lean_inc_ref(v_b_6566_);
                    lean_dec_ref_known(v_x_6528_, 2);
                    v___x_6567_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6565_);
                    v___x_6568_ = lean_obj_once(
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
                    v_a_6572_ = lean_ctor_get(v_x_6528_, 0);
                    lean_inc_ref(v_a_6572_);
                    v_b_6573_ = lean_ctor_get(v_x_6528_, 1);
                    lean_inc_ref(v_b_6573_);
                    lean_dec_ref_known(v_x_6528_, 2);
                    v___x_6574_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6572_);
                    v___x_6575_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_6573_);
                    v___x_6576_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_6574_, v___x_6575_);
                    return v___x_6576_;
                }
                _ => {
                    v_a_6577_ = lean_ctor_get(v_x_6528_, 0);
                    v_k_6578_ = lean_ctor_get(v_x_6528_, 1);
                    v_isSharedCheck_6610_ = (!lean_is_exclusive(v_x_6528_)) as u8;
                    if v_isSharedCheck_6610_ == 0 {
                        v___x_6580_ = v_x_6528_;
                        v_isShared_6581_ = v_isSharedCheck_6610_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_k_6578_);
                        lean_inc(v_a_6577_);
                        lean_dec(v_x_6528_);
                        v___x_6580_ = lean_box(0);
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
                    v_reuseFailAlloc_6535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6535_, 0, v_k_6529_);
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
                    lean_ctor_set_tag(v___x_6539_, 0);
                    lean_ctor_set(v___x_6539_, 0, v___x_6541_);
                    v___x_6543_ = v___x_6539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6544_, 0, v___x_6541_);
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
                    lean_ctor_set_tag(v___x_6548_, 0);
                    v___x_6551_ = v___x_6548_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6552_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_k_6546_);
                    v___x_6551_ = v_reuseFailAlloc_6552_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6551_;
            }
            7 => {
                v___x_6586_ = lean_unsigned_to_nat(0);
                v___x_6587_ = lean_nat_dec_eq(v_k_6578_, v___x_6586_);
                if v___x_6587_ == 0 {
                    match lean_obj_tag(v_a_6577_) {
                        0 => {
                            lean_del_object(v___x_6580_);
                            v_k_6588_ = lean_ctor_get(v_a_6577_, 0);
                            lean_inc(v_k_6588_);
                            lean_dec_ref_known(v_a_6577_, 1);
                            v_n_6583_ = v_k_6588_;
                            state = 8;
                            continue;
                        }
                        2 => {
                            lean_del_object(v___x_6580_);
                            v_k_6589_ = lean_ctor_get(v_a_6577_, 0);
                            lean_inc(v_k_6589_);
                            lean_dec_ref_known(v_a_6577_, 1);
                            v_n_6583_ = v_k_6589_;
                            state = 8;
                            continue;
                        }
                        1 => {
                            lean_del_object(v___x_6580_);
                            v_k_6590_ = lean_ctor_get(v_a_6577_, 0);
                            v_isSharedCheck_6599_ = (!lean_is_exclusive(v_a_6577_)) as u8;
                            if v_isSharedCheck_6599_ == 0 {
                                v___x_6592_ = v_a_6577_;
                                v_isShared_6593_ = v_isSharedCheck_6599_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_k_6590_);
                                lean_dec(v_a_6577_);
                                v___x_6592_ = lean_box(0);
                                v_isShared_6593_ = v_isSharedCheck_6599_;
                                state = 9;
                                continue;
                            }
                        }
                        3 => {
                            v_i_6600_ = lean_ctor_get(v_a_6577_, 0);
                            lean_inc(v_i_6600_);
                            lean_dec_ref_known(v_a_6577_, 1);
                            if v_isShared_6581_ == 0 {
                                lean_ctor_set_tag(v___x_6580_, 0);
                                lean_ctor_set(v___x_6580_, 0, v_i_6600_);
                                v___x_6602_ = v___x_6580_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_6606_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_i_6600_);
                                lean_ctor_set(v_reuseFailAlloc_6606_, 1, v_k_6578_);
                                v___x_6602_ = v_reuseFailAlloc_6606_;
                                state = 11;
                                continue;
                            }
                        }
                        _ => {
                            lean_del_object(v___x_6580_);
                            v___x_6607_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_6577_);
                            v___x_6608_ =
                                l_Lean_Grind_CommRing_Poly_pow__nc(v___x_6607_, v_k_6578_);
                            lean_dec(v_k_6578_);
                            return v___x_6608_;
                        }
                    }
                } else {
                    lean_del_object(v___x_6580_);
                    lean_dec(v_k_6578_);
                    lean_dec_ref(v_a_6577_);
                    v___x_6609_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_6609_;
                }
            }
            8 => {
                v___x_6584_ = l_Int_pow(v_n_6583_, v_k_6578_);
                lean_dec(v_k_6578_);
                lean_dec(v_n_6583_);
                v___x_6585_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6585_, 0, v___x_6584_);
                return v___x_6585_;
            }
            9 => {
                v___x_6594_ = lean_nat_to_int(v_k_6590_);
                v___x_6595_ = l_Int_pow(v___x_6594_, v_k_6578_);
                lean_dec(v_k_6578_);
                lean_dec(v___x_6594_);
                if v_isShared_6593_ == 0 {
                    lean_ctor_set_tag(v___x_6592_, 0);
                    lean_ctor_set(v___x_6592_, 0, v___x_6595_);
                    v___x_6597_ = v___x_6592_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6595_);
                    v___x_6597_ = v_reuseFailAlloc_6598_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6597_;
            }
            11 => {
                v___x_6603_ = lean_box(0);
                v___x_6604_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6604_, 0, v___x_6602_);
                lean_ctor_set(v___x_6604_, 1, v___x_6603_);
                v___x_6605_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_6604_);
                return v___x_6605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_normEq0(
    mut v_p_6611_: *mut LeanObject,
    mut v_c_6612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: u8 = 0;
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6624_: u8 = 0;
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: u8 = 0;
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_6611_) == 0 {
                    v_k_6613_ = lean_ctor_get(v_p_6611_, 0);
                    v___x_6614_ = lean_nat_to_int(v_c_6612_);
                    v___x_6615_ = lean_int_emod(v_k_6613_, v___x_6614_);
                    lean_dec(v___x_6614_);
                    v___x_6616_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                    );
                    v___x_6617_ = lean_int_dec_eq(v___x_6615_, v___x_6616_);
                    lean_dec(v___x_6615_);
                    if v___x_6617_ == 0 {
                        return v_p_6611_;
                    } else {
                        lean_dec_ref_known(v_p_6611_, 1);
                        v___x_6618_ = lean_obj_once(
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
                    v_k_6619_ = lean_ctor_get(v_p_6611_, 0);
                    v_v_6620_ = lean_ctor_get(v_p_6611_, 1);
                    v_p_6621_ = lean_ctor_get(v_p_6611_, 2);
                    v_isSharedCheck_6634_ = (!lean_is_exclusive(v_p_6611_)) as u8;
                    if v_isSharedCheck_6634_ == 0 {
                        v___x_6623_ = v_p_6611_;
                        v_isShared_6624_ = v_isSharedCheck_6634_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_6621_);
                        lean_inc(v_v_6620_);
                        lean_inc(v_k_6619_);
                        lean_dec(v_p_6611_);
                        v___x_6623_ = lean_box(0);
                        v_isShared_6624_ = v_isSharedCheck_6634_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_c_6612_);
                v___x_6625_ = lean_nat_to_int(v_c_6612_);
                v___x_6626_ = lean_int_emod(v_k_6619_, v___x_6625_);
                lean_dec(v___x_6625_);
                v___x_6627_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
                );
                v___x_6628_ = lean_int_dec_eq(v___x_6626_, v___x_6627_);
                lean_dec(v___x_6626_);
                if v___x_6628_ == 0 {
                    v___x_6629_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_6621_, v_c_6612_);
                    if v_isShared_6624_ == 0 {
                        lean_ctor_set(v___x_6623_, 2, v___x_6629_);
                        v___x_6631_ = v___x_6623_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6632_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_k_6619_);
                        lean_ctor_set(v_reuseFailAlloc_6632_, 1, v_v_6620_);
                        lean_ctor_set(v_reuseFailAlloc_6632_, 2, v___x_6629_);
                        v___x_6631_ = v_reuseFailAlloc_6632_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6623_);
                    lean_dec(v_v_6620_);
                    lean_dec(v_k_6619_);
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
    mut v_p_6635_: *mut LeanObject,
    mut v_k_6636_: *mut LeanObject,
    mut v_c_6637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6641_: u8 = 0;
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6648_: u8 = 0;
    let mut v_k_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6654_: u8 = 0;
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_6635_) == 0 {
                    v_k_6638_ = lean_ctor_get(v_p_6635_, 0);
                    v_isSharedCheck_6648_ = (!lean_is_exclusive(v_p_6635_)) as u8;
                    if v_isSharedCheck_6648_ == 0 {
                        v___x_6640_ = v_p_6635_;
                        v_isShared_6641_ = v_isSharedCheck_6648_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_6638_);
                        lean_dec(v_p_6635_);
                        v___x_6640_ = lean_box(0);
                        v_isShared_6641_ = v_isSharedCheck_6648_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_6649_ = lean_ctor_get(v_p_6635_, 0);
                    v_v_6650_ = lean_ctor_get(v_p_6635_, 1);
                    v_p_6651_ = lean_ctor_get(v_p_6635_, 2);
                    v_isSharedCheck_6659_ = (!lean_is_exclusive(v_p_6635_)) as u8;
                    if v_isSharedCheck_6659_ == 0 {
                        v___x_6653_ = v_p_6635_;
                        v_isShared_6654_ = v_isSharedCheck_6659_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_p_6651_);
                        lean_inc(v_v_6650_);
                        lean_inc(v_k_6649_);
                        lean_dec(v_p_6635_);
                        v___x_6653_ = lean_box(0);
                        v_isShared_6654_ = v_isSharedCheck_6659_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6642_ = lean_int_add(v_k_6638_, v_k_6636_);
                lean_dec(v_k_6638_);
                v___x_6643_ = lean_nat_to_int(v_c_6637_);
                v___x_6644_ = lean_int_emod(v___x_6642_, v___x_6643_);
                lean_dec(v___x_6643_);
                lean_dec(v___x_6642_);
                if v_isShared_6641_ == 0 {
                    lean_ctor_set(v___x_6640_, 0, v___x_6644_);
                    v___x_6646_ = v___x_6640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6647_, 0, v___x_6644_);
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
                    lean_ctor_set(v___x_6653_, 2, v___x_6655_);
                    v___x_6657_ = v___x_6653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6658_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6658_, 0, v_k_6649_);
                    lean_ctor_set(v_reuseFailAlloc_6658_, 1, v_v_6650_);
                    lean_ctor_set(v_reuseFailAlloc_6658_, 2, v___x_6655_);
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
    mut v_p_6660_: *mut LeanObject,
    mut v_k_6661_: *mut LeanObject,
    mut v_c_6662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6663_: *mut LeanObject = core::ptr::null_mut();
    v_res_6663_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_6660_, v_k_6661_, v_c_6662_);
    lean_dec(v_k_6661_);
    return v_res_6663_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insertC_go(
    mut v_m_6664_: *mut LeanObject,
    mut v_c_6665_: *mut LeanObject,
    mut v_k_6666_: *mut LeanObject,
    mut v_a_6667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: u8 = 0;
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6675_: u8 = 0;
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6680_: u8 = 0;
    let mut v_unused_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_x27_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: u8 = 0;
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6695_: u8 = 0;
    let mut v_unused_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6667_) == 0 {
                    lean_dec(v_c_6665_);
                    v___x_6668_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_6668_, 0, v_k_6666_);
                    lean_ctor_set(v___x_6668_, 1, v_m_6664_);
                    lean_ctor_set(v___x_6668_, 2, v_a_6667_);
                    return v___x_6668_;
                } else {
                    v_k_6669_ = lean_ctor_get(v_a_6667_, 0);
                    v_v_6670_ = lean_ctor_get(v_a_6667_, 1);
                    v_p_6671_ = lean_ctor_get(v_a_6667_, 2);
                    v___x_6672_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_6664_, v_v_6670_);
                    match v___x_6672_ {
                        0 => {
                            lean_inc_ref(v_p_6671_);
                            lean_inc(v_v_6670_);
                            lean_inc(v_k_6669_);
                            v_isSharedCheck_6680_ = (!lean_is_exclusive(v_a_6667_)) as u8;
                            if v_isSharedCheck_6680_ == 0 {
                                v_unused_6681_ = lean_ctor_get(v_a_6667_, 2);
                                lean_dec(v_unused_6681_);
                                v_unused_6682_ = lean_ctor_get(v_a_6667_, 1);
                                lean_dec(v_unused_6682_);
                                v_unused_6683_ = lean_ctor_get(v_a_6667_, 0);
                                lean_dec(v_unused_6683_);
                                v___x_6674_ = v_a_6667_;
                                v_isShared_6675_ = v_isSharedCheck_6680_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_6667_);
                                v___x_6674_ = lean_box(0);
                                v_isShared_6675_ = v_isSharedCheck_6680_;
                                state = 1;
                                continue;
                            }
                        }
                        1 => {
                            lean_inc_ref(v_p_6671_);
                            lean_inc(v_k_6669_);
                            v_isSharedCheck_6695_ = (!lean_is_exclusive(v_a_6667_)) as u8;
                            if v_isSharedCheck_6695_ == 0 {
                                v_unused_6696_ = lean_ctor_get(v_a_6667_, 2);
                                lean_dec(v_unused_6696_);
                                v_unused_6697_ = lean_ctor_get(v_a_6667_, 1);
                                lean_dec(v_unused_6697_);
                                v_unused_6698_ = lean_ctor_get(v_a_6667_, 0);
                                lean_dec(v_unused_6698_);
                                v___x_6685_ = v_a_6667_;
                                v_isShared_6686_ = v_isSharedCheck_6695_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_a_6667_);
                                v___x_6685_ = lean_box(0);
                                v_isShared_6686_ = v_isSharedCheck_6695_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_c_6665_);
                            v___x_6699_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_6699_, 0, v_k_6666_);
                            lean_ctor_set(v___x_6699_, 1, v_m_6664_);
                            lean_ctor_set(v___x_6699_, 2, v_a_6667_);
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
                    lean_ctor_set(v___x_6674_, 2, v___x_6676_);
                    v___x_6678_ = v___x_6674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6679_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_k_6669_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 1, v_v_6670_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 2, v___x_6676_);
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
                lean_dec(v_k_6669_);
                lean_dec(v_k_6666_);
                v___x_6688_ = lean_nat_to_int(v_c_6665_);
                v_k_x27_x27_6689_ = lean_int_emod(v___x_6687_, v___x_6688_);
                lean_dec(v___x_6688_);
                lean_dec(v___x_6687_);
                v___x_6690_ = lean_obj_once(
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
                        lean_ctor_set(v___x_6685_, 1, v_m_6664_);
                        lean_ctor_set(v___x_6685_, 0, v_k_x27_x27_6689_);
                        v___x_6693_ = v___x_6685_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6694_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_k_x27_x27_6689_);
                        lean_ctor_set(v_reuseFailAlloc_6694_, 1, v_m_6664_);
                        lean_ctor_set(v_reuseFailAlloc_6694_, 2, v_p_6671_);
                        v___x_6693_ = v_reuseFailAlloc_6694_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_k_x27_x27_6689_);
                    lean_del_object(v___x_6685_);
                    lean_dec(v_m_6664_);
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
    mut v_k_6700_: *mut LeanObject,
    mut v_m_6701_: *mut LeanObject,
    mut v_p_6702_: *mut LeanObject,
    mut v_c_6703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: u8 = 0;
    lean_inc(v_c_6703_);
    v___x_6704_ = lean_nat_to_int(v_c_6703_);
    v_k_6705_ = lean_int_emod(v_k_6700_, v___x_6704_);
    lean_dec(v___x_6704_);
    v___x_6706_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6707_ = lean_int_dec_eq(v_k_6705_, v___x_6706_);
    if v___x_6707_ == 0 {
        let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
        v___x_6708_ =
            l_Lean_Grind_CommRing_Poly_insertC_go(v_m_6701_, v_c_6703_, v_k_6705_, v_p_6702_);
        return v___x_6708_;
    } else {
        lean_dec(v_k_6705_);
        lean_dec(v_c_6703_);
        lean_dec(v_m_6701_);
        return v_p_6702_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_insertC___boxed(
    mut v_k_6709_: *mut LeanObject,
    mut v_m_6710_: *mut LeanObject,
    mut v_p_6711_: *mut LeanObject,
    mut v_c_6712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6713_: *mut LeanObject = core::ptr::null_mut();
    v_res_6713_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_6709_, v_m_6710_, v_p_6711_, v_c_6712_);
    lean_dec(v_k_6709_);
    return v_res_6713_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstC_go(
    mut v_k_6714_: *mut LeanObject,
    mut v_c_6715_: *mut LeanObject,
    mut v_a_6716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6720_: u8 = 0;
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6727_: u8 = 0;
    let mut v_k_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6733_: u8 = 0;
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: u8 = 0;
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6716_) == 0 {
                    v_k_6717_ = lean_ctor_get(v_a_6716_, 0);
                    v_isSharedCheck_6727_ = (!lean_is_exclusive(v_a_6716_)) as u8;
                    if v_isSharedCheck_6727_ == 0 {
                        v___x_6719_ = v_a_6716_;
                        v_isShared_6720_ = v_isSharedCheck_6727_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_6717_);
                        lean_dec(v_a_6716_);
                        v___x_6719_ = lean_box(0);
                        v_isShared_6720_ = v_isSharedCheck_6727_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_6728_ = lean_ctor_get(v_a_6716_, 0);
                    v_v_6729_ = lean_ctor_get(v_a_6716_, 1);
                    v_p_6730_ = lean_ctor_get(v_a_6716_, 2);
                    v_isSharedCheck_6744_ = (!lean_is_exclusive(v_a_6716_)) as u8;
                    if v_isSharedCheck_6744_ == 0 {
                        v___x_6732_ = v_a_6716_;
                        v_isShared_6733_ = v_isSharedCheck_6744_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_p_6730_);
                        lean_inc(v_v_6729_);
                        lean_inc(v_k_6728_);
                        lean_dec(v_a_6716_);
                        v___x_6732_ = lean_box(0);
                        v_isShared_6733_ = v_isSharedCheck_6744_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6721_ = lean_int_mul(v_k_6714_, v_k_6717_);
                lean_dec(v_k_6717_);
                v___x_6722_ = lean_nat_to_int(v_c_6715_);
                v___x_6723_ = lean_int_emod(v___x_6721_, v___x_6722_);
                lean_dec(v___x_6722_);
                lean_dec(v___x_6721_);
                if v_isShared_6720_ == 0 {
                    lean_ctor_set(v___x_6719_, 0, v___x_6723_);
                    v___x_6725_ = v___x_6719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 0, v___x_6723_);
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
                lean_dec(v_k_6728_);
                lean_inc(v_c_6715_);
                v___x_6735_ = lean_nat_to_int(v_c_6715_);
                v_k_6736_ = lean_int_emod(v___x_6734_, v___x_6735_);
                lean_dec(v___x_6735_);
                lean_dec(v___x_6734_);
                v___x_6737_ = lean_obj_once(
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
                        lean_ctor_set(v___x_6732_, 2, v___x_6739_);
                        lean_ctor_set(v___x_6732_, 0, v_k_6736_);
                        v___x_6741_ = v___x_6732_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6742_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_k_6736_);
                        lean_ctor_set(v_reuseFailAlloc_6742_, 1, v_v_6729_);
                        lean_ctor_set(v_reuseFailAlloc_6742_, 2, v___x_6739_);
                        v___x_6741_ = v_reuseFailAlloc_6742_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_k_6736_);
                    lean_del_object(v___x_6732_);
                    lean_dec(v_v_6729_);
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
    mut v_k_6745_: *mut LeanObject,
    mut v_c_6746_: *mut LeanObject,
    mut v_a_6747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6748_: *mut LeanObject = core::ptr::null_mut();
    v_res_6748_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_6745_, v_c_6746_, v_a_6747_);
    lean_dec(v_k_6745_);
    return v_res_6748_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstC(
    mut v_k_6749_: *mut LeanObject,
    mut v_p_6750_: *mut LeanObject,
    mut v_c_6751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: u8 = 0;
    lean_inc(v_c_6751_);
    v___x_6752_ = lean_nat_to_int(v_c_6751_);
    v_k_6753_ = lean_int_emod(v_k_6749_, v___x_6752_);
    lean_dec(v___x_6752_);
    v___x_6754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6755_ = lean_int_dec_eq(v_k_6753_, v___x_6754_);
    if v___x_6755_ == 0 {
        let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6757_: u8 = 0;
        v___x_6756_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once),
            _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4,
        );
        v___x_6757_ = lean_int_dec_eq(v_k_6753_, v___x_6756_);
        lean_dec(v_k_6753_);
        if v___x_6757_ == 0 {
            let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
            v___x_6758_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_6749_, v_c_6751_, v_p_6750_);
            return v___x_6758_;
        } else {
            lean_dec(v_c_6751_);
            return v_p_6750_;
        }
    } else {
        let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_6753_);
        lean_dec(v_c_6751_);
        lean_dec_ref(v_p_6750_);
        v___x_6759_ = lean_obj_once(
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
    mut v_k_6760_: *mut LeanObject,
    mut v_p_6761_: *mut LeanObject,
    mut v_c_6762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6763_: *mut LeanObject = core::ptr::null_mut();
    v_res_6763_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6760_, v_p_6761_, v_c_6762_);
    lean_dec(v_k_6760_);
    return v_res_6763_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC_go(
    mut v_k_6764_: *mut LeanObject,
    mut v_m_6765_: *mut LeanObject,
    mut v_c_6766_: *mut LeanObject,
    mut v_a_6767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: u8 = 0;
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: u8 = 0;
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6767_) == 0 {
                    v_k_6768_ = lean_ctor_get(v_a_6767_, 0);
                    lean_inc(v_k_6768_);
                    lean_dec_ref_known(v_a_6767_, 1);
                    v___x_6769_ = lean_int_mul(v_k_6764_, v_k_6768_);
                    lean_dec(v_k_6768_);
                    v___x_6770_ = lean_nat_to_int(v_c_6766_);
                    v_k_6771_ = lean_int_emod(v___x_6769_, v___x_6770_);
                    lean_dec(v___x_6770_);
                    lean_dec(v___x_6769_);
                    v___x_6772_ = lean_obj_once(
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
                        v___x_6774_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0,
                        );
                        v___x_6775_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_6775_, 0, v_k_6771_);
                        lean_ctor_set(v___x_6775_, 1, v_m_6765_);
                        lean_ctor_set(v___x_6775_, 2, v___x_6774_);
                        return v___x_6775_;
                    } else {
                        lean_dec(v_k_6771_);
                        lean_dec(v_m_6765_);
                        v___x_6776_ = lean_obj_once(
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
                    v_k_6777_ = lean_ctor_get(v_a_6767_, 0);
                    v_v_6778_ = lean_ctor_get(v_a_6767_, 1);
                    v_p_6779_ = lean_ctor_get(v_a_6767_, 2);
                    v_isSharedCheck_6794_ = (!lean_is_exclusive(v_a_6767_)) as u8;
                    if v_isSharedCheck_6794_ == 0 {
                        v___x_6781_ = v_a_6767_;
                        v_isShared_6782_ = v_isSharedCheck_6794_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_6779_);
                        lean_inc(v_v_6778_);
                        lean_inc(v_k_6777_);
                        lean_dec(v_a_6767_);
                        v___x_6781_ = lean_box(0);
                        v_isShared_6782_ = v_isSharedCheck_6794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6783_ = lean_int_mul(v_k_6764_, v_k_6777_);
                lean_dec(v_k_6777_);
                lean_inc(v_c_6766_);
                v___x_6784_ = lean_nat_to_int(v_c_6766_);
                v_k_6785_ = lean_int_emod(v___x_6783_, v___x_6784_);
                lean_dec(v___x_6784_);
                lean_dec(v___x_6783_);
                v___x_6786_ = lean_obj_once(
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
                    lean_inc(v_m_6765_);
                    v___x_6788_ = l_Lean_Grind_CommRing_Mon_mul(v_m_6765_, v_v_6778_);
                    v___x_6789_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(
                        v_k_6764_, v_m_6765_, v_c_6766_, v_p_6779_,
                    );
                    if v_isShared_6782_ == 0 {
                        lean_ctor_set(v___x_6781_, 2, v___x_6789_);
                        lean_ctor_set(v___x_6781_, 1, v___x_6788_);
                        lean_ctor_set(v___x_6781_, 0, v_k_6785_);
                        v___x_6791_ = v___x_6781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6792_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6792_, 0, v_k_6785_);
                        lean_ctor_set(v_reuseFailAlloc_6792_, 1, v___x_6788_);
                        lean_ctor_set(v_reuseFailAlloc_6792_, 2, v___x_6789_);
                        v___x_6791_ = v_reuseFailAlloc_6792_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_6785_);
                    lean_del_object(v___x_6781_);
                    lean_dec(v_v_6778_);
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
    mut v_k_6795_: *mut LeanObject,
    mut v_m_6796_: *mut LeanObject,
    mut v_c_6797_: *mut LeanObject,
    mut v_a_6798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6799_: *mut LeanObject = core::ptr::null_mut();
    v_res_6799_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_6795_, v_m_6796_, v_c_6797_, v_a_6798_);
    lean_dec(v_k_6795_);
    return v_res_6799_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC(
    mut v_k_6800_: *mut LeanObject,
    mut v_m_6801_: *mut LeanObject,
    mut v_p_6802_: *mut LeanObject,
    mut v_c_6803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    lean_inc(v_c_6803_);
    v___x_6804_ = lean_nat_to_int(v_c_6803_);
    v_k_6805_ = lean_int_emod(v_k_6800_, v___x_6804_);
    lean_dec(v___x_6804_);
    v___x_6806_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6807_ = lean_int_dec_eq(v_k_6805_, v___x_6806_);
    if v___x_6807_ == 0 {
        let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6809_: u8 = 0;
        v___x_6808_ = lean_box(0);
        v___x_6809_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6801_, v___x_6808_);
        if v___x_6809_ == 0 {
            let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_6805_);
            v___x_6810_ =
                l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_6800_, v_m_6801_, v_c_6803_, v_p_6802_);
            return v___x_6810_;
        } else {
            let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_m_6801_);
            v___x_6811_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6805_, v_p_6802_, v_c_6803_);
            lean_dec(v_k_6805_);
            return v___x_6811_;
        }
    } else {
        let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_6805_);
        lean_dec(v_c_6803_);
        lean_dec_ref(v_p_6802_);
        lean_dec(v_m_6801_);
        v___x_6812_ = lean_obj_once(
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
    mut v_k_6813_: *mut LeanObject,
    mut v_m_6814_: *mut LeanObject,
    mut v_p_6815_: *mut LeanObject,
    mut v_c_6816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6817_: *mut LeanObject = core::ptr::null_mut();
    v_res_6817_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_6813_, v_m_6814_, v_p_6815_, v_c_6816_);
    lean_dec(v_k_6813_);
    return v_res_6817_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(
    mut v_k_6818_: *mut LeanObject,
    mut v_m_6819_: *mut LeanObject,
    mut v_c_6820_: *mut LeanObject,
    mut v_p_6821_: *mut LeanObject,
    mut v_acc_6822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_6821_) == 0 {
                    v_k_6823_ = lean_ctor_get(v_p_6821_, 0);
                    lean_inc(v_k_6823_);
                    lean_dec_ref_known(v_p_6821_, 1);
                    v___x_6824_ = lean_int_mul(v_k_6818_, v_k_6823_);
                    lean_dec(v_k_6823_);
                    v___x_6825_ = lean_nat_to_int(v_c_6820_);
                    v___x_6826_ = lean_int_emod(v___x_6824_, v___x_6825_);
                    lean_dec(v___x_6825_);
                    lean_dec(v___x_6824_);
                    v___x_6827_ =
                        l_Lean_Grind_CommRing_Poly_insert(v___x_6826_, v_m_6819_, v_acc_6822_);
                    return v___x_6827_;
                } else {
                    v_k_6828_ = lean_ctor_get(v_p_6821_, 0);
                    lean_inc(v_k_6828_);
                    v_v_6829_ = lean_ctor_get(v_p_6821_, 1);
                    lean_inc(v_v_6829_);
                    v_p_6830_ = lean_ctor_get(v_p_6821_, 2);
                    lean_inc_ref(v_p_6830_);
                    lean_dec_ref_known(v_p_6821_, 3);
                    v___x_6831_ = lean_int_mul(v_k_6818_, v_k_6828_);
                    lean_dec(v_k_6828_);
                    lean_inc(v_c_6820_);
                    v___x_6832_ = lean_nat_to_int(v_c_6820_);
                    v___x_6833_ = lean_int_emod(v___x_6831_, v___x_6832_);
                    lean_dec(v___x_6832_);
                    lean_dec(v___x_6831_);
                    lean_inc(v_m_6819_);
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
    mut v_k_6837_: *mut LeanObject,
    mut v_m_6838_: *mut LeanObject,
    mut v_c_6839_: *mut LeanObject,
    mut v_p_6840_: *mut LeanObject,
    mut v_acc_6841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6842_: *mut LeanObject = core::ptr::null_mut();
    v_res_6842_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(
        v_k_6837_,
        v_m_6838_,
        v_c_6839_,
        v_p_6840_,
        v_acc_6841_,
    );
    lean_dec(v_k_6837_);
    return v_res_6842_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonC__nc(
    mut v_k_6843_: *mut LeanObject,
    mut v_m_6844_: *mut LeanObject,
    mut v_p_6845_: *mut LeanObject,
    mut v_c_6846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u8 = 0;
    lean_inc(v_c_6846_);
    v___x_6847_ = lean_nat_to_int(v_c_6846_);
    v_k_6848_ = lean_int_emod(v_k_6843_, v___x_6847_);
    lean_dec(v___x_6847_);
    v___x_6849_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once),
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
    );
    v___x_6850_ = lean_int_dec_eq(v_k_6848_, v___x_6849_);
    if v___x_6850_ == 0 {
        let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6852_: u8 = 0;
        v___x_6851_ = lean_box(0);
        v___x_6852_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_6844_, v___x_6851_);
        if v___x_6852_ == 0 {
            let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_6848_);
            v___x_6853_ = lean_obj_once(
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
            let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_m_6844_);
            v___x_6855_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6848_, v_p_6845_, v_c_6846_);
            lean_dec(v_k_6848_);
            return v___x_6855_;
        }
    } else {
        let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_6848_);
        lean_dec(v_c_6846_);
        lean_dec_ref(v_p_6845_);
        lean_dec(v_m_6844_);
        v___x_6856_ = lean_obj_once(
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
    mut v_k_6857_: *mut LeanObject,
    mut v_m_6858_: *mut LeanObject,
    mut v_p_6859_: *mut LeanObject,
    mut v_c_6860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6861_: *mut LeanObject = core::ptr::null_mut();
    v_res_6861_ =
        l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_6857_, v_m_6858_, v_p_6859_, v_c_6860_);
    lean_dec(v_k_6857_);
    return v_res_6861_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combineC(
    mut v_p_u2081_6862_: *mut LeanObject,
    mut v_p_u2082_6863_: *mut LeanObject,
    mut v_c_6864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6869_: u8 = 0;
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6876_: u8 = 0;
    let mut v_k_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: u8 = 0;
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6890_: u8 = 0;
    let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6895_: u8 = 0;
    let mut v_unused_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6901_: u8 = 0;
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: u8 = 0;
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6912_: u8 = 0;
    let mut v_unused_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6923_: u8 = 0;
    let mut v_unused_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_6862_) == 0 {
                    if lean_obj_tag(v_p_u2082_6863_) == 0 {
                        v_k_6865_ = lean_ctor_get(v_p_u2081_6862_, 0);
                        lean_inc(v_k_6865_);
                        lean_dec_ref_known(v_p_u2081_6862_, 1);
                        v_k_6866_ = lean_ctor_get(v_p_u2082_6863_, 0);
                        v_isSharedCheck_6876_ = (!lean_is_exclusive(v_p_u2082_6863_)) as u8;
                        if v_isSharedCheck_6876_ == 0 {
                            v___x_6868_ = v_p_u2082_6863_;
                            v_isShared_6869_ = v_isSharedCheck_6876_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_k_6866_);
                            lean_dec(v_p_u2082_6863_);
                            v___x_6868_ = lean_box(0);
                            v_isShared_6869_ = v_isSharedCheck_6876_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_k_6877_ = lean_ctor_get(v_p_u2081_6862_, 0);
                        lean_inc(v_k_6877_);
                        lean_dec_ref_known(v_p_u2081_6862_, 1);
                        v___x_6878_ = l_Lean_Grind_CommRing_Poly_addConstC(
                            v_p_u2082_6863_,
                            v_k_6877_,
                            v_c_6864_,
                        );
                        lean_dec(v_k_6877_);
                        return v___x_6878_;
                    }
                } else {
                    if lean_obj_tag(v_p_u2082_6863_) == 0 {
                        v_k_6879_ = lean_ctor_get(v_p_u2082_6863_, 0);
                        lean_inc(v_k_6879_);
                        lean_dec_ref_known(v_p_u2082_6863_, 1);
                        v___x_6880_ = l_Lean_Grind_CommRing_Poly_addConstC(
                            v_p_u2081_6862_,
                            v_k_6879_,
                            v_c_6864_,
                        );
                        lean_dec(v_k_6879_);
                        return v___x_6880_;
                    } else {
                        v_k_6881_ = lean_ctor_get(v_p_u2081_6862_, 0);
                        v_v_6882_ = lean_ctor_get(v_p_u2081_6862_, 1);
                        v_p_6883_ = lean_ctor_get(v_p_u2081_6862_, 2);
                        v_k_6884_ = lean_ctor_get(v_p_u2082_6863_, 0);
                        v_v_6885_ = lean_ctor_get(v_p_u2082_6863_, 1);
                        v_p_6886_ = lean_ctor_get(v_p_u2082_6863_, 2);
                        v___x_6887_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_6882_, v_v_6885_);
                        match v___x_6887_ {
                            0 => {
                                lean_inc_ref(v_p_6886_);
                                lean_inc(v_v_6885_);
                                lean_inc(v_k_6884_);
                                v_isSharedCheck_6895_ = (!lean_is_exclusive(v_p_u2082_6863_)) as u8;
                                if v_isSharedCheck_6895_ == 0 {
                                    v_unused_6896_ = lean_ctor_get(v_p_u2082_6863_, 2);
                                    lean_dec(v_unused_6896_);
                                    v_unused_6897_ = lean_ctor_get(v_p_u2082_6863_, 1);
                                    lean_dec(v_unused_6897_);
                                    v_unused_6898_ = lean_ctor_get(v_p_u2082_6863_, 0);
                                    lean_dec(v_unused_6898_);
                                    v___x_6889_ = v_p_u2082_6863_;
                                    v_isShared_6890_ = v_isSharedCheck_6895_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2082_6863_);
                                    v___x_6889_ = lean_box(0);
                                    v_isShared_6890_ = v_isSharedCheck_6895_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                lean_inc_ref(v_p_6886_);
                                lean_inc(v_k_6884_);
                                lean_inc_ref(v_p_6883_);
                                lean_inc(v_v_6882_);
                                lean_inc(v_k_6881_);
                                lean_dec_ref_known(v_p_u2081_6862_, 3);
                                v_isSharedCheck_6912_ = (!lean_is_exclusive(v_p_u2082_6863_)) as u8;
                                if v_isSharedCheck_6912_ == 0 {
                                    v_unused_6913_ = lean_ctor_get(v_p_u2082_6863_, 2);
                                    lean_dec(v_unused_6913_);
                                    v_unused_6914_ = lean_ctor_get(v_p_u2082_6863_, 1);
                                    lean_dec(v_unused_6914_);
                                    v_unused_6915_ = lean_ctor_get(v_p_u2082_6863_, 0);
                                    lean_dec(v_unused_6915_);
                                    v___x_6900_ = v_p_u2082_6863_;
                                    v_isShared_6901_ = v_isSharedCheck_6912_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2082_6863_);
                                    v___x_6900_ = lean_box(0);
                                    v_isShared_6901_ = v_isSharedCheck_6912_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                lean_inc_ref(v_p_6883_);
                                lean_inc(v_v_6882_);
                                lean_inc(v_k_6881_);
                                v_isSharedCheck_6923_ = (!lean_is_exclusive(v_p_u2081_6862_)) as u8;
                                if v_isSharedCheck_6923_ == 0 {
                                    v_unused_6924_ = lean_ctor_get(v_p_u2081_6862_, 2);
                                    lean_dec(v_unused_6924_);
                                    v_unused_6925_ = lean_ctor_get(v_p_u2081_6862_, 1);
                                    lean_dec(v_unused_6925_);
                                    v_unused_6926_ = lean_ctor_get(v_p_u2081_6862_, 0);
                                    lean_dec(v_unused_6926_);
                                    v___x_6917_ = v_p_u2081_6862_;
                                    v_isShared_6918_ = v_isSharedCheck_6923_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2081_6862_);
                                    v___x_6917_ = lean_box(0);
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
                lean_dec(v_k_6866_);
                lean_dec(v_k_6865_);
                v___x_6871_ = lean_nat_to_int(v_c_6864_);
                v___x_6872_ = lean_int_emod(v___x_6870_, v___x_6871_);
                lean_dec(v___x_6871_);
                lean_dec(v___x_6870_);
                if v_isShared_6869_ == 0 {
                    lean_ctor_set(v___x_6868_, 0, v___x_6872_);
                    v___x_6874_ = v___x_6868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6875_, 0, v___x_6872_);
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
                    lean_ctor_set(v___x_6889_, 2, v___x_6891_);
                    v___x_6893_ = v___x_6889_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6894_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6894_, 0, v_k_6884_);
                    lean_ctor_set(v_reuseFailAlloc_6894_, 1, v_v_6885_);
                    lean_ctor_set(v_reuseFailAlloc_6894_, 2, v___x_6891_);
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
                lean_dec(v_k_6884_);
                lean_dec(v_k_6881_);
                lean_inc(v_c_6864_);
                v___x_6903_ = lean_nat_to_int(v_c_6864_);
                v_k_6904_ = lean_int_emod(v___x_6902_, v___x_6903_);
                lean_dec(v___x_6903_);
                lean_dec(v___x_6902_);
                v___x_6905_ = lean_obj_once(
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
                        lean_ctor_set(v___x_6900_, 2, v___x_6907_);
                        lean_ctor_set(v___x_6900_, 1, v_v_6882_);
                        lean_ctor_set(v___x_6900_, 0, v_k_6904_);
                        v___x_6909_ = v___x_6900_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6910_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6910_, 0, v_k_6904_);
                        lean_ctor_set(v_reuseFailAlloc_6910_, 1, v_v_6882_);
                        lean_ctor_set(v_reuseFailAlloc_6910_, 2, v___x_6907_);
                        v___x_6909_ = v_reuseFailAlloc_6910_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_k_6904_);
                    lean_del_object(v___x_6900_);
                    lean_dec(v_v_6882_);
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
                    lean_ctor_set(v___x_6917_, 2, v___x_6919_);
                    v___x_6921_ = v___x_6917_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6922_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_k_6881_);
                    lean_ctor_set(v_reuseFailAlloc_6922_, 1, v_v_6882_);
                    lean_ctor_set(v_reuseFailAlloc_6922_, 2, v___x_6919_);
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
    mut v_p_u2082_6927_: *mut LeanObject,
    mut v_c_6928_: *mut LeanObject,
    mut v_p_u2081_6929_: *mut LeanObject,
    mut v_acc_6930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_6929_) == 0 {
                    v_k_6931_ = lean_ctor_get(v_p_u2081_6929_, 0);
                    lean_inc(v_k_6931_);
                    lean_dec_ref_known(v_p_u2081_6929_, 1);
                    lean_inc(v_c_6928_);
                    v___x_6932_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6931_, v_p_u2082_6927_, v_c_6928_);
                    lean_dec(v_k_6931_);
                    v___x_6933_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_acc_6930_, v___x_6932_, v_c_6928_);
                    return v___x_6933_;
                } else {
                    v_k_6934_ = lean_ctor_get(v_p_u2081_6929_, 0);
                    lean_inc(v_k_6934_);
                    v_v_6935_ = lean_ctor_get(v_p_u2081_6929_, 1);
                    lean_inc(v_v_6935_);
                    v_p_6936_ = lean_ctor_get(v_p_u2081_6929_, 2);
                    lean_inc_ref(v_p_6936_);
                    lean_dec_ref_known(v_p_u2081_6929_, 3);
                    lean_inc_n(v_c_6928_, 2);
                    lean_inc_ref(v_p_u2082_6927_);
                    v___x_6937_ = l_Lean_Grind_CommRing_Poly_mulMonC(
                        v_k_6934_,
                        v_v_6935_,
                        v_p_u2082_6927_,
                        v_c_6928_,
                    );
                    lean_dec(v_k_6934_);
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
    mut v_p_u2081_6940_: *mut LeanObject,
    mut v_p_u2082_6941_: *mut LeanObject,
    mut v_c_6942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    v___x_6943_ = lean_obj_once(
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
    mut v_p_u2082_6945_: *mut LeanObject,
    mut v_c_6946_: *mut LeanObject,
    mut v_p_u2081_6947_: *mut LeanObject,
    mut v_acc_6948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_6947_) == 0 {
                    v_k_6949_ = lean_ctor_get(v_p_u2081_6947_, 0);
                    lean_inc(v_k_6949_);
                    lean_dec_ref_known(v_p_u2081_6947_, 1);
                    lean_inc(v_c_6946_);
                    v___x_6950_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v_k_6949_, v_p_u2082_6945_, v_c_6946_);
                    lean_dec(v_k_6949_);
                    v___x_6951_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v_acc_6948_, v___x_6950_, v_c_6946_);
                    return v___x_6951_;
                } else {
                    v_k_6952_ = lean_ctor_get(v_p_u2081_6947_, 0);
                    lean_inc(v_k_6952_);
                    v_v_6953_ = lean_ctor_get(v_p_u2081_6947_, 1);
                    lean_inc(v_v_6953_);
                    v_p_6954_ = lean_ctor_get(v_p_u2081_6947_, 2);
                    lean_inc_ref(v_p_6954_);
                    lean_dec_ref_known(v_p_u2081_6947_, 3);
                    lean_inc_n(v_c_6946_, 2);
                    lean_inc_ref(v_p_u2082_6945_);
                    v___x_6955_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(
                        v_k_6952_,
                        v_v_6953_,
                        v_p_u2082_6945_,
                        v_c_6946_,
                    );
                    lean_dec(v_k_6952_);
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
    mut v_p_u2081_6958_: *mut LeanObject,
    mut v_p_u2082_6959_: *mut LeanObject,
    mut v_c_6960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    v___x_6961_ = lean_obj_once(
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
    mut v_p_6963_: *mut LeanObject,
    mut v_k_6964_: *mut LeanObject,
    mut v_c_6965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6967_: u8 = 0;
    v_zero_6966_ = lean_unsigned_to_nat(0);
    v_isZero_6967_ = lean_nat_dec_eq(v_k_6964_, v_zero_6966_);
    if v_isZero_6967_ == 1 {
        let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_c_6965_);
        lean_dec_ref(v_p_6963_);
        v___x_6968_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6968_;
    } else {
        let mut v_one_6969_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_6970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6971_: u8 = 0;
        v_one_6969_ = lean_unsigned_to_nat(1);
        v_n_6970_ = lean_nat_sub(v_k_6964_, v_one_6969_);
        v___x_6971_ = lean_nat_dec_eq(v_n_6970_, v_zero_6966_);
        if v___x_6971_ == 0 {
            let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_c_6965_);
            lean_inc_ref(v_p_6963_);
            v___x_6972_ = l_Lean_Grind_CommRing_Poly_powC(v_p_6963_, v_n_6970_, v_c_6965_);
            lean_dec(v_n_6970_);
            v___x_6973_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_6963_, v___x_6972_, v_c_6965_);
            return v___x_6973_;
        } else {
            lean_dec(v_n_6970_);
            lean_dec(v_c_6965_);
            return v_p_6963_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC___boxed(
    mut v_p_6974_: *mut LeanObject,
    mut v_k_6975_: *mut LeanObject,
    mut v_c_6976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6977_: *mut LeanObject = core::ptr::null_mut();
    v_res_6977_ = l_Lean_Grind_CommRing_Poly_powC(v_p_6974_, v_k_6975_, v_c_6976_);
    lean_dec(v_k_6975_);
    return v_res_6977_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC__nc(
    mut v_p_6978_: *mut LeanObject,
    mut v_k_6979_: *mut LeanObject,
    mut v_c_6980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6982_: u8 = 0;
    v_zero_6981_ = lean_unsigned_to_nat(0);
    v_isZero_6982_ = lean_nat_dec_eq(v_k_6979_, v_zero_6981_);
    if v_isZero_6982_ == 1 {
        let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_c_6980_);
        lean_dec_ref(v_p_6978_);
        v___x_6983_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
        );
        return v___x_6983_;
    } else {
        let mut v_one_6984_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_6985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6986_: u8 = 0;
        v_one_6984_ = lean_unsigned_to_nat(1);
        v_n_6985_ = lean_nat_sub(v_k_6979_, v_one_6984_);
        v___x_6986_ = lean_nat_dec_eq(v_n_6985_, v_zero_6981_);
        if v___x_6986_ == 0 {
            let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_c_6980_);
            lean_inc_ref(v_p_6978_);
            v___x_6987_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_6978_, v_n_6985_, v_c_6980_);
            lean_dec(v_n_6985_);
            v___x_6988_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_6987_, v_p_6978_, v_c_6980_);
            return v___x_6988_;
        } else {
            lean_dec(v_n_6985_);
            lean_dec(v_c_6980_);
            return v_p_6978_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_powC__nc___boxed(
    mut v_p_6989_: *mut LeanObject,
    mut v_k_6990_: *mut LeanObject,
    mut v_c_6991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6992_: *mut LeanObject = core::ptr::null_mut();
    v_res_6992_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_6989_, v_k_6990_, v_c_6991_);
    lean_dec(v_k_6990_);
    return v_res_6992_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC_go(
    mut v_c_6993_: *mut LeanObject,
    mut v_a_6994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v_i_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7038_: u8 = 0;
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: u8 = 0;
    let mut v_k_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7044_: u8 = 0;
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7051_: u8 = 0;
    let mut v_i_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v_k_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_6994_) {
                1 => {
                    v_k_7000_ = lean_ctor_get(v_a_6994_, 0);
                    v_isSharedCheck_7010_ = (!lean_is_exclusive(v_a_6994_)) as u8;
                    if v_isSharedCheck_7010_ == 0 {
                        v___x_7002_ = v_a_6994_;
                        v_isShared_7003_ = v_isSharedCheck_7010_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_7000_);
                        lean_dec(v_a_6994_);
                        v___x_7002_ = lean_box(0);
                        v_isShared_7003_ = v_isSharedCheck_7010_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    lean_dec(v_c_6993_);
                    v_i_7011_ = lean_ctor_get(v_a_6994_, 0);
                    lean_inc(v_i_7011_);
                    lean_dec_ref_known(v_a_6994_, 1);
                    v___x_7012_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_7011_);
                    return v___x_7012_;
                }
                4 => {
                    v_a_7013_ = lean_ctor_get(v_a_6994_, 0);
                    lean_inc_ref(v_a_7013_);
                    lean_dec_ref_known(v_a_6994_, 1);
                    v___x_7014_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    lean_inc(v_c_6993_);
                    v___x_7015_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7013_);
                    v___x_7016_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v___x_7014_, v___x_7015_, v_c_6993_);
                    return v___x_7016_;
                }
                5 => {
                    v_a_7017_ = lean_ctor_get(v_a_6994_, 0);
                    lean_inc_ref(v_a_7017_);
                    v_b_7018_ = lean_ctor_get(v_a_6994_, 1);
                    lean_inc_ref(v_b_7018_);
                    lean_dec_ref_known(v_a_6994_, 2);
                    lean_inc_n(v_c_6993_, 2);
                    v___x_7019_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7017_);
                    v___x_7020_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_b_7018_);
                    v___x_7021_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v___x_7019_, v___x_7020_, v_c_6993_);
                    return v___x_7021_;
                }
                6 => {
                    v_a_7022_ = lean_ctor_get(v_a_6994_, 0);
                    lean_inc_ref(v_a_7022_);
                    v_b_7023_ = lean_ctor_get(v_a_6994_, 1);
                    lean_inc_ref(v_b_7023_);
                    lean_dec_ref_known(v_a_6994_, 2);
                    lean_inc_n(v_c_6993_, 3);
                    v___x_7024_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7022_);
                    v___x_7025_ = lean_obj_once(
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
                    v_a_7029_ = lean_ctor_get(v_a_6994_, 0);
                    lean_inc_ref(v_a_7029_);
                    v_b_7030_ = lean_ctor_get(v_a_6994_, 1);
                    lean_inc_ref(v_b_7030_);
                    lean_dec_ref_known(v_a_6994_, 2);
                    lean_inc_n(v_c_6993_, 2);
                    v___x_7031_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7029_);
                    v___x_7032_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_b_7030_);
                    v___x_7033_ =
                        l_Lean_Grind_CommRing_Poly_mulC(v___x_7031_, v___x_7032_, v_c_6993_);
                    return v___x_7033_;
                }
                8 => {
                    v_a_7034_ = lean_ctor_get(v_a_6994_, 0);
                    v_k_7035_ = lean_ctor_get(v_a_6994_, 1);
                    v_isSharedCheck_7062_ = (!lean_is_exclusive(v_a_6994_)) as u8;
                    if v_isSharedCheck_7062_ == 0 {
                        v___x_7037_ = v_a_6994_;
                        v_isShared_7038_ = v_isSharedCheck_7062_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_k_7035_);
                        lean_inc(v_a_7034_);
                        lean_dec(v_a_6994_);
                        v___x_7037_ = lean_box(0);
                        v_isShared_7038_ = v_isSharedCheck_7062_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_k_7063_ = lean_ctor_get(v_a_6994_, 0);
                    lean_inc(v_k_7063_);
                    lean_dec_ref(v_a_6994_);
                    v_k_6996_ = v_k_7063_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_6997_ = lean_nat_to_int(v_c_6993_);
                v___x_6998_ = lean_int_emod(v_k_6996_, v___x_6997_);
                lean_dec(v___x_6997_);
                lean_dec(v_k_6996_);
                v___x_6999_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6999_, 0, v___x_6998_);
                return v___x_6999_;
            }
            2 => {
                v___x_7004_ = lean_nat_to_int(v_k_7000_);
                v___x_7005_ = lean_nat_to_int(v_c_6993_);
                v___x_7006_ = lean_int_emod(v___x_7004_, v___x_7005_);
                lean_dec(v___x_7005_);
                lean_dec(v___x_7004_);
                if v_isShared_7003_ == 0 {
                    lean_ctor_set_tag(v___x_7002_, 0);
                    lean_ctor_set(v___x_7002_, 0, v___x_7006_);
                    v___x_7008_ = v___x_7002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7009_, 0, v___x_7006_);
                    v___x_7008_ = v_reuseFailAlloc_7009_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7008_;
            }
            4 => {
                v___x_7039_ = lean_unsigned_to_nat(0);
                v___x_7040_ = lean_nat_dec_eq(v_k_7035_, v___x_7039_);
                if v___x_7040_ == 0 {
                    match lean_obj_tag(v_a_7034_) {
                        0 => {
                            lean_del_object(v___x_7037_);
                            v_k_7041_ = lean_ctor_get(v_a_7034_, 0);
                            v_isSharedCheck_7051_ = (!lean_is_exclusive(v_a_7034_)) as u8;
                            if v_isSharedCheck_7051_ == 0 {
                                v___x_7043_ = v_a_7034_;
                                v_isShared_7044_ = v_isSharedCheck_7051_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_k_7041_);
                                lean_dec(v_a_7034_);
                                v___x_7043_ = lean_box(0);
                                v_isShared_7044_ = v_isSharedCheck_7051_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            lean_dec(v_c_6993_);
                            v_i_7052_ = lean_ctor_get(v_a_7034_, 0);
                            lean_inc(v_i_7052_);
                            lean_dec_ref_known(v_a_7034_, 1);
                            if v_isShared_7038_ == 0 {
                                lean_ctor_set_tag(v___x_7037_, 0);
                                lean_ctor_set(v___x_7037_, 0, v_i_7052_);
                                v___x_7054_ = v___x_7037_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_7058_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_i_7052_);
                                lean_ctor_set(v_reuseFailAlloc_7058_, 1, v_k_7035_);
                                v___x_7054_ = v_reuseFailAlloc_7058_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            lean_del_object(v___x_7037_);
                            lean_inc(v_c_6993_);
                            v___x_7059_ =
                                l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_6993_, v_a_7034_);
                            v___x_7060_ =
                                l_Lean_Grind_CommRing_Poly_powC(v___x_7059_, v_k_7035_, v_c_6993_);
                            lean_dec(v_k_7035_);
                            return v___x_7060_;
                        }
                    }
                } else {
                    lean_del_object(v___x_7037_);
                    lean_dec(v_k_7035_);
                    lean_dec_ref(v_a_7034_);
                    lean_dec(v_c_6993_);
                    v___x_7061_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_7061_;
                }
            }
            5 => {
                v___x_7045_ = l_Int_pow(v_k_7041_, v_k_7035_);
                lean_dec(v_k_7035_);
                lean_dec(v_k_7041_);
                v___x_7046_ = lean_nat_to_int(v_c_6993_);
                v___x_7047_ = lean_int_emod(v___x_7045_, v___x_7046_);
                lean_dec(v___x_7046_);
                lean_dec(v___x_7045_);
                if v_isShared_7044_ == 0 {
                    lean_ctor_set(v___x_7043_, 0, v___x_7047_);
                    v___x_7049_ = v___x_7043_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7050_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_7047_);
                    v___x_7049_ = v_reuseFailAlloc_7050_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7049_;
            }
            7 => {
                v___x_7055_ = lean_box(0);
                v___x_7056_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7056_, 0, v___x_7054_);
                lean_ctor_set(v___x_7056_, 1, v___x_7055_);
                v___x_7057_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_7056_);
                return v___x_7057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC(
    mut v_e_7064_: *mut LeanObject,
    mut v_c_7065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    v___x_7066_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_7065_, v_e_7064_);
    return v___x_7066_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(
    mut v_c_7067_: *mut LeanObject,
    mut v_a_7068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7077_: u8 = 0;
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7084_: u8 = 0;
    let mut v_i_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7112_: u8 = 0;
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: u8 = 0;
    let mut v_k_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7118_: u8 = 0;
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7125_: u8 = 0;
    let mut v_i_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7136_: u8 = 0;
    let mut v_k_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_7068_) {
                1 => {
                    v_k_7074_ = lean_ctor_get(v_a_7068_, 0);
                    v_isSharedCheck_7084_ = (!lean_is_exclusive(v_a_7068_)) as u8;
                    if v_isSharedCheck_7084_ == 0 {
                        v___x_7076_ = v_a_7068_;
                        v_isShared_7077_ = v_isSharedCheck_7084_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_7074_);
                        lean_dec(v_a_7068_);
                        v___x_7076_ = lean_box(0);
                        v_isShared_7077_ = v_isSharedCheck_7084_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    lean_dec(v_c_7067_);
                    v_i_7085_ = lean_ctor_get(v_a_7068_, 0);
                    lean_inc(v_i_7085_);
                    lean_dec_ref_known(v_a_7068_, 1);
                    v___x_7086_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_7085_);
                    return v___x_7086_;
                }
                4 => {
                    v_a_7087_ = lean_ctor_get(v_a_7068_, 0);
                    lean_inc_ref(v_a_7087_);
                    lean_dec_ref_known(v_a_7068_, 1);
                    v___x_7088_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0,
                    );
                    lean_inc(v_c_7067_);
                    v___x_7089_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7087_);
                    v___x_7090_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v___x_7088_, v___x_7089_, v_c_7067_);
                    return v___x_7090_;
                }
                5 => {
                    v_a_7091_ = lean_ctor_get(v_a_7068_, 0);
                    lean_inc_ref(v_a_7091_);
                    v_b_7092_ = lean_ctor_get(v_a_7068_, 1);
                    lean_inc_ref(v_b_7092_);
                    lean_dec_ref_known(v_a_7068_, 2);
                    lean_inc_n(v_c_7067_, 2);
                    v___x_7093_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7091_);
                    v___x_7094_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_b_7092_);
                    v___x_7095_ =
                        l_Lean_Grind_CommRing_Poly_combineC(v___x_7093_, v___x_7094_, v_c_7067_);
                    return v___x_7095_;
                }
                6 => {
                    v_a_7096_ = lean_ctor_get(v_a_7068_, 0);
                    lean_inc_ref(v_a_7096_);
                    v_b_7097_ = lean_ctor_get(v_a_7068_, 1);
                    lean_inc_ref(v_b_7097_);
                    lean_dec_ref_known(v_a_7068_, 2);
                    lean_inc_n(v_c_7067_, 3);
                    v___x_7098_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7096_);
                    v___x_7099_ = lean_obj_once(
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
                    v_a_7103_ = lean_ctor_get(v_a_7068_, 0);
                    lean_inc_ref(v_a_7103_);
                    v_b_7104_ = lean_ctor_get(v_a_7068_, 1);
                    lean_inc_ref(v_b_7104_);
                    lean_dec_ref_known(v_a_7068_, 2);
                    lean_inc_n(v_c_7067_, 2);
                    v___x_7105_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7103_);
                    v___x_7106_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_b_7104_);
                    v___x_7107_ =
                        l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_7105_, v___x_7106_, v_c_7067_);
                    return v___x_7107_;
                }
                8 => {
                    v_a_7108_ = lean_ctor_get(v_a_7068_, 0);
                    v_k_7109_ = lean_ctor_get(v_a_7068_, 1);
                    v_isSharedCheck_7136_ = (!lean_is_exclusive(v_a_7068_)) as u8;
                    if v_isSharedCheck_7136_ == 0 {
                        v___x_7111_ = v_a_7068_;
                        v_isShared_7112_ = v_isSharedCheck_7136_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_k_7109_);
                        lean_inc(v_a_7108_);
                        lean_dec(v_a_7068_);
                        v___x_7111_ = lean_box(0);
                        v_isShared_7112_ = v_isSharedCheck_7136_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_k_7137_ = lean_ctor_get(v_a_7068_, 0);
                    lean_inc(v_k_7137_);
                    lean_dec_ref(v_a_7068_);
                    v_k_7070_ = v_k_7137_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_7071_ = lean_nat_to_int(v_c_7067_);
                v___x_7072_ = lean_int_emod(v_k_7070_, v___x_7071_);
                lean_dec(v___x_7071_);
                lean_dec(v_k_7070_);
                v___x_7073_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7073_, 0, v___x_7072_);
                return v___x_7073_;
            }
            2 => {
                v___x_7078_ = lean_nat_to_int(v_k_7074_);
                v___x_7079_ = lean_nat_to_int(v_c_7067_);
                v___x_7080_ = lean_int_emod(v___x_7078_, v___x_7079_);
                lean_dec(v___x_7079_);
                lean_dec(v___x_7078_);
                if v_isShared_7077_ == 0 {
                    lean_ctor_set_tag(v___x_7076_, 0);
                    lean_ctor_set(v___x_7076_, 0, v___x_7080_);
                    v___x_7082_ = v___x_7076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7083_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7083_, 0, v___x_7080_);
                    v___x_7082_ = v_reuseFailAlloc_7083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7082_;
            }
            4 => {
                v___x_7113_ = lean_unsigned_to_nat(0);
                v___x_7114_ = lean_nat_dec_eq(v_k_7109_, v___x_7113_);
                if v___x_7114_ == 0 {
                    match lean_obj_tag(v_a_7108_) {
                        0 => {
                            lean_del_object(v___x_7111_);
                            v_k_7115_ = lean_ctor_get(v_a_7108_, 0);
                            v_isSharedCheck_7125_ = (!lean_is_exclusive(v_a_7108_)) as u8;
                            if v_isSharedCheck_7125_ == 0 {
                                v___x_7117_ = v_a_7108_;
                                v_isShared_7118_ = v_isSharedCheck_7125_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_k_7115_);
                                lean_dec(v_a_7108_);
                                v___x_7117_ = lean_box(0);
                                v_isShared_7118_ = v_isSharedCheck_7125_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            lean_dec(v_c_7067_);
                            v_i_7126_ = lean_ctor_get(v_a_7108_, 0);
                            lean_inc(v_i_7126_);
                            lean_dec_ref_known(v_a_7108_, 1);
                            if v_isShared_7112_ == 0 {
                                lean_ctor_set_tag(v___x_7111_, 0);
                                lean_ctor_set(v___x_7111_, 0, v_i_7126_);
                                v___x_7128_ = v___x_7111_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_7132_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7132_, 0, v_i_7126_);
                                lean_ctor_set(v_reuseFailAlloc_7132_, 1, v_k_7109_);
                                v___x_7128_ = v_reuseFailAlloc_7132_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            lean_del_object(v___x_7111_);
                            lean_inc(v_c_7067_);
                            v___x_7133_ =
                                l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7067_, v_a_7108_);
                            v___x_7134_ = l_Lean_Grind_CommRing_Poly_powC__nc(
                                v___x_7133_,
                                v_k_7109_,
                                v_c_7067_,
                            );
                            lean_dec(v_k_7109_);
                            return v___x_7134_;
                        }
                    }
                } else {
                    lean_del_object(v___x_7111_);
                    lean_dec(v_k_7109_);
                    lean_dec_ref(v_a_7108_);
                    lean_dec(v_c_7067_);
                    v___x_7135_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_pow___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_pow___closed__0,
                    );
                    return v___x_7135_;
                }
            }
            5 => {
                v___x_7119_ = l_Int_pow(v_k_7115_, v_k_7109_);
                lean_dec(v_k_7109_);
                lean_dec(v_k_7115_);
                v___x_7120_ = lean_nat_to_int(v_c_7067_);
                v___x_7121_ = lean_int_emod(v___x_7119_, v___x_7120_);
                lean_dec(v___x_7120_);
                lean_dec(v___x_7119_);
                if v_isShared_7118_ == 0 {
                    lean_ctor_set(v___x_7117_, 0, v___x_7121_);
                    v___x_7123_ = v___x_7117_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7124_, 0, v___x_7121_);
                    v___x_7123_ = v_reuseFailAlloc_7124_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7123_;
            }
            7 => {
                v___x_7129_ = lean_box(0);
                v___x_7130_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7130_, 0, v___x_7128_);
                lean_ctor_set(v___x_7130_, 1, v___x_7129_);
                v___x_7131_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_7130_);
                return v___x_7131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyC__nc(
    mut v_e_7138_: *mut LeanObject,
    mut v_c_7139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    v___x_7140_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_7139_, v_e_7138_);
    return v___x_7140_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(
    mut v_x_7141_: *mut LeanObject,
    mut v_h__1_7142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    v_x_7143_ = lean_ctor_get(v_x_7141_, 0);
    lean_inc(v_x_7143_);
    v_k_7144_ = lean_ctor_get(v_x_7141_, 1);
    lean_inc(v_k_7144_);
    lean_dec_ref(v_x_7141_);
    v___x_7145_ = lean_apply_2(v_h__1_7142_, v_x_7143_, v_k_7144_);
    return v___x_7145_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(
    mut v_motive_7146_: *mut LeanObject,
    mut v_x_7147_: *mut LeanObject,
    mut v_h__1_7148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    v_x_7149_ = lean_ctor_get(v_x_7147_, 0);
    lean_inc(v_x_7149_);
    v_k_7150_ = lean_ctor_get(v_x_7147_, 1);
    lean_inc(v_k_7150_);
    lean_dec_ref(v_x_7147_);
    v___x_7151_ = lean_apply_2(v_h__1_7148_, v_x_7149_, v_k_7150_);
    return v___x_7151_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(
    mut v_k_7152_: *mut LeanObject,
    mut v_h__1_7153_: *mut LeanObject,
    mut v_h__2_7154_: *mut LeanObject,
    mut v_h__3_7155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: u8 = 0;
    v___x_7156_ = lean_unsigned_to_nat(0);
    v___x_7157_ = lean_nat_dec_eq(v_k_7152_, v___x_7156_);
    if v___x_7157_ == 0 {
        let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7159_: u8 = 0;
        lean_dec(v_h__1_7153_);
        v___x_7158_ = lean_unsigned_to_nat(1);
        v___x_7159_ = lean_nat_dec_eq(v_k_7152_, v___x_7158_);
        if v___x_7159_ == 0 {
            let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_7154_);
            v___x_7160_ = lean_apply_3(v_h__3_7155_, v_k_7152_, lean_box(0), lean_box(0));
            return v___x_7160_;
        } else {
            let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7155_);
            lean_dec(v_k_7152_);
            v___x_7161_ = lean_box(0);
            v___x_7162_ = lean_apply_1(v_h__2_7154_, v___x_7161_);
            return v___x_7162_;
        }
    } else {
        let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_7155_);
        lean_dec(v_h__2_7154_);
        lean_dec(v_k_7152_);
        v___x_7163_ = lean_box(0);
        v___x_7164_ = lean_apply_1(v_h__1_7153_, v___x_7163_);
        return v___x_7164_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(
    mut v_motive_7165_: *mut LeanObject,
    mut v_k_7166_: *mut LeanObject,
    mut v_h__1_7167_: *mut LeanObject,
    mut v_h__2_7168_: *mut LeanObject,
    mut v_h__3_7169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    v___x_7170_ = lean_unsigned_to_nat(0);
    v___x_7171_ = lean_nat_dec_eq(v_k_7166_, v___x_7170_);
    if v___x_7171_ == 0 {
        let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7173_: u8 = 0;
        lean_dec(v_h__1_7167_);
        v___x_7172_ = lean_unsigned_to_nat(1);
        v___x_7173_ = lean_nat_dec_eq(v_k_7166_, v___x_7172_);
        if v___x_7173_ == 0 {
            let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_7168_);
            v___x_7174_ = lean_apply_3(v_h__3_7169_, v_k_7166_, lean_box(0), lean_box(0));
            return v___x_7174_;
        } else {
            let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7169_);
            lean_dec(v_k_7166_);
            v___x_7175_ = lean_box(0);
            v___x_7176_ = lean_apply_1(v_h__2_7168_, v___x_7175_);
            return v___x_7176_;
        }
    } else {
        let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_7169_);
        lean_dec(v_h__2_7168_);
        lean_dec(v_k_7166_);
        v___x_7177_ = lean_box(0);
        v___x_7178_ = lean_apply_1(v_h__1_7167_, v___x_7177_);
        return v___x_7178_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(
    mut v_m_u2081_7179_: *mut LeanObject,
    mut v_h__1_7180_: *mut LeanObject,
    mut v_h__2_7181_: *mut LeanObject,
    mut v_h__3_7182_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2081_7179_) == 0 {
        let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_7182_);
        lean_dec(v_h__2_7181_);
        v___x_7183_ = lean_box(0);
        v___x_7184_ = lean_apply_1(v_h__1_7180_, v___x_7183_);
        return v___x_7184_;
    } else {
        let mut v_m_7185_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_7180_);
        v_m_7185_ = lean_ctor_get(v_m_u2081_7179_, 1);
        if lean_obj_tag(v_m_7185_) == 0 {
            let mut v_p_7186_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7187_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7182_);
            v_p_7186_ = lean_ctor_get(v_m_u2081_7179_, 0);
            lean_inc_ref(v_p_7186_);
            lean_dec_ref_known(v_m_u2081_7179_, 2);
            v___x_7187_ = lean_apply_1(v_h__2_7181_, v_p_7186_);
            return v___x_7187_;
        } else {
            let mut v_p_7188_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7189_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_m_7185_);
            lean_dec(v_h__2_7181_);
            v_p_7188_ = lean_ctor_get(v_m_u2081_7179_, 0);
            lean_inc_ref(v_p_7188_);
            lean_dec_ref_known(v_m_u2081_7179_, 2);
            v___x_7189_ = lean_apply_3(v_h__3_7182_, v_p_7188_, v_m_7185_, lean_box(0));
            return v___x_7189_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(
    mut v_motive_7190_: *mut LeanObject,
    mut v_m_u2081_7191_: *mut LeanObject,
    mut v_h__1_7192_: *mut LeanObject,
    mut v_h__2_7193_: *mut LeanObject,
    mut v_h__3_7194_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2081_7191_) == 0 {
        let mut v___x_7195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_7194_);
        lean_dec(v_h__2_7193_);
        v___x_7195_ = lean_box(0);
        v___x_7196_ = lean_apply_1(v_h__1_7192_, v___x_7195_);
        return v___x_7196_;
    } else {
        let mut v_m_7197_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_7192_);
        v_m_7197_ = lean_ctor_get(v_m_u2081_7191_, 1);
        if lean_obj_tag(v_m_7197_) == 0 {
            let mut v_p_7198_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7194_);
            v_p_7198_ = lean_ctor_get(v_m_u2081_7191_, 0);
            lean_inc_ref(v_p_7198_);
            lean_dec_ref_known(v_m_u2081_7191_, 2);
            v___x_7199_ = lean_apply_1(v_h__2_7193_, v_p_7198_);
            return v___x_7199_;
        } else {
            let mut v_p_7200_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_m_7197_);
            lean_dec(v_h__2_7193_);
            v_p_7200_ = lean_ctor_get(v_m_u2081_7191_, 0);
            lean_inc_ref(v_p_7200_);
            lean_dec_ref_known(v_m_u2081_7191_, 2);
            v___x_7201_ = lean_apply_3(v_h__3_7194_, v_p_7200_, v_m_7197_, lean_box(0));
            return v___x_7201_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(
    mut v_a_7202_: u8,
    mut v_h__1_7203_: *mut LeanObject,
    mut v_h__2_7204_: *mut LeanObject,
) -> *mut LeanObject {
    if v_a_7202_ == 1 {
        let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_7204_);
        v___x_7205_ = lean_box(0);
        v___x_7206_ = lean_apply_1(v_h__1_7203_, v___x_7205_);
        return v___x_7206_;
    } else {
        let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_7203_);
        v___x_7207_ = lean_box((v_a_7202_) as usize);
        v___x_7208_ = lean_apply_2(v_h__2_7204_, v___x_7207_, lean_box(0));
        return v___x_7208_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(
    mut v_a_7209_: *mut LeanObject,
    mut v_h__1_7210_: *mut LeanObject,
    mut v_h__2_7211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_17__boxed_7212_: u8 = 0;
    let mut v_res_7213_: *mut LeanObject = core::ptr::null_mut();
    v_a_17__boxed_7212_ = (lean_unbox(v_a_7209_) as u8);
    v_res_7213_ =
        l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(
            v_a_17__boxed_7212_,
            v_h__1_7210_,
            v_h__2_7211_,
        );
    return v_res_7213_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(
    mut v_motive_7214_: *mut LeanObject,
    mut v_a_7215_: u8,
    mut v_h__1_7216_: *mut LeanObject,
    mut v_h__2_7217_: *mut LeanObject,
) -> *mut LeanObject {
    if v_a_7215_ == 1 {
        let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_7217_);
        v___x_7218_ = lean_box(0);
        v___x_7219_ = lean_apply_1(v_h__1_7216_, v___x_7218_);
        return v___x_7219_;
    } else {
        let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_7216_);
        v___x_7220_ = lean_box((v_a_7215_) as usize);
        v___x_7221_ = lean_apply_2(v_h__2_7217_, v___x_7220_, lean_box(0));
        return v___x_7221_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(
    mut v_motive_7222_: *mut LeanObject,
    mut v_a_7223_: *mut LeanObject,
    mut v_h__1_7224_: *mut LeanObject,
    mut v_h__2_7225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_28__boxed_7226_: u8 = 0;
    let mut v_res_7227_: *mut LeanObject = core::ptr::null_mut();
    v_a_28__boxed_7226_ = (lean_unbox(v_a_7223_) as u8);
    v_res_7227_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(
        v_motive_7222_,
        v_a_28__boxed_7226_,
        v_h__1_7224_,
        v_h__2_7225_,
    );
    return v_res_7227_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(
    mut v_p_7228_: *mut LeanObject,
    mut v_h__1_7229_: *mut LeanObject,
    mut v_h__2_7230_: *mut LeanObject,
    mut v_h__3_7231_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_7228_) == 0 {
        let mut v_k_7232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7234_: u8 = 0;
        lean_dec(v_h__3_7231_);
        v_k_7232_ = lean_ctor_get(v_p_7228_, 0);
        lean_inc(v_k_7232_);
        lean_dec_ref_known(v_p_7228_, 1);
        v___x_7233_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
        );
        v___x_7234_ = lean_int_dec_eq(v_k_7232_, v___x_7233_);
        if v___x_7234_ == 0 {
            let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_7229_);
            v___x_7235_ = lean_apply_2(v_h__2_7230_, v_k_7232_, lean_box(0));
            return v___x_7235_;
        } else {
            let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_7232_);
            lean_dec(v_h__2_7230_);
            v___x_7236_ = lean_box(0);
            v___x_7237_ = lean_apply_1(v_h__1_7229_, v___x_7236_);
            return v___x_7237_;
        }
    } else {
        let mut v_k_7238_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_7239_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_7240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_7230_);
        lean_dec(v_h__1_7229_);
        v_k_7238_ = lean_ctor_get(v_p_7228_, 0);
        lean_inc(v_k_7238_);
        v_v_7239_ = lean_ctor_get(v_p_7228_, 1);
        lean_inc(v_v_7239_);
        v_p_7240_ = lean_ctor_get(v_p_7228_, 2);
        lean_inc_ref(v_p_7240_);
        lean_dec_ref_known(v_p_7228_, 3);
        v___x_7241_ = lean_apply_3(v_h__3_7231_, v_k_7238_, v_v_7239_, v_p_7240_);
        return v___x_7241_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(
    mut v_motive_7242_: *mut LeanObject,
    mut v_p_7243_: *mut LeanObject,
    mut v_h__1_7244_: *mut LeanObject,
    mut v_h__2_7245_: *mut LeanObject,
    mut v_h__3_7246_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_7243_) == 0 {
        let mut v_k_7247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7249_: u8 = 0;
        lean_dec(v_h__3_7246_);
        v_k_7247_ = lean_ctor_get(v_p_7243_, 0);
        lean_inc(v_k_7247_);
        lean_dec_ref_known(v_p_7243_, 1);
        v___x_7248_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once
            ),
            _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0,
        );
        v___x_7249_ = lean_int_dec_eq(v_k_7247_, v___x_7248_);
        if v___x_7249_ == 0 {
            let mut v___x_7250_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_7244_);
            v___x_7250_ = lean_apply_2(v_h__2_7245_, v_k_7247_, lean_box(0));
            return v___x_7250_;
        } else {
            let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_7247_);
            lean_dec(v_h__2_7245_);
            v___x_7251_ = lean_box(0);
            v___x_7252_ = lean_apply_1(v_h__1_7244_, v___x_7251_);
            return v___x_7252_;
        }
    } else {
        let mut v_k_7253_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_7254_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_7255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_7245_);
        lean_dec(v_h__1_7244_);
        v_k_7253_ = lean_ctor_get(v_p_7243_, 0);
        lean_inc(v_k_7253_);
        v_v_7254_ = lean_ctor_get(v_p_7243_, 1);
        lean_inc(v_v_7254_);
        v_p_7255_ = lean_ctor_get(v_p_7243_, 2);
        lean_inc_ref(v_p_7255_);
        lean_dec_ref_known(v_p_7243_, 3);
        v___x_7256_ = lean_apply_3(v_h__3_7246_, v_k_7253_, v_v_7254_, v_p_7255_);
        return v___x_7256_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(
    mut v_k_7257_: *mut LeanObject,
    mut v_h__1_7258_: *mut LeanObject,
    mut v_h__2_7259_: *mut LeanObject,
    mut v_h__3_7260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7262_: u8 = 0;
    v_zero_7261_ = lean_unsigned_to_nat(0);
    v_isZero_7262_ = lean_nat_dec_eq(v_k_7257_, v_zero_7261_);
    if v_isZero_7262_ == 1 {
        let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7264_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_7260_);
        lean_dec(v_h__2_7259_);
        v___x_7263_ = lean_box(0);
        v___x_7264_ = lean_apply_1(v_h__1_7258_, v___x_7263_);
        return v___x_7264_;
    } else {
        let mut v_one_7265_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_7266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7267_: u8 = 0;
        lean_dec(v_h__1_7258_);
        v_one_7265_ = lean_unsigned_to_nat(1);
        v_n_7266_ = lean_nat_sub(v_k_7257_, v_one_7265_);
        v___x_7267_ = lean_nat_dec_eq(v_n_7266_, v_zero_7261_);
        if v___x_7267_ == 0 {
            let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_7259_);
            v___x_7268_ = lean_apply_2(v_h__3_7260_, v_n_7266_, lean_box(0));
            return v___x_7268_;
        } else {
            let mut v___x_7269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_n_7266_);
            lean_dec(v_h__3_7260_);
            v___x_7269_ = lean_box(0);
            v___x_7270_ = lean_apply_1(v_h__2_7259_, v___x_7269_);
            return v___x_7270_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(
    mut v_k_7271_: *mut LeanObject,
    mut v_h__1_7272_: *mut LeanObject,
    mut v_h__2_7273_: *mut LeanObject,
    mut v_h__3_7274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7275_: *mut LeanObject = core::ptr::null_mut();
    v_res_7275_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_7271_, v_h__1_7272_, v_h__2_7273_, v_h__3_7274_);
    lean_dec(v_k_7271_);
    return v_res_7275_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(
    mut v_motive_7276_: *mut LeanObject,
    mut v_k_7277_: *mut LeanObject,
    mut v_h__1_7278_: *mut LeanObject,
    mut v_h__2_7279_: *mut LeanObject,
    mut v_h__3_7280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7282_: u8 = 0;
    v_zero_7281_ = lean_unsigned_to_nat(0);
    v_isZero_7282_ = lean_nat_dec_eq(v_k_7277_, v_zero_7281_);
    if v_isZero_7282_ == 1 {
        let mut v___x_7283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_7280_);
        lean_dec(v_h__2_7279_);
        v___x_7283_ = lean_box(0);
        v___x_7284_ = lean_apply_1(v_h__1_7278_, v___x_7283_);
        return v___x_7284_;
    } else {
        let mut v_one_7285_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_7286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7287_: u8 = 0;
        lean_dec(v_h__1_7278_);
        v_one_7285_ = lean_unsigned_to_nat(1);
        v_n_7286_ = lean_nat_sub(v_k_7277_, v_one_7285_);
        v___x_7287_ = lean_nat_dec_eq(v_n_7286_, v_zero_7281_);
        if v___x_7287_ == 0 {
            let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_7279_);
            v___x_7288_ = lean_apply_2(v_h__3_7280_, v_n_7286_, lean_box(0));
            return v___x_7288_;
        } else {
            let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_n_7286_);
            lean_dec(v_h__3_7280_);
            v___x_7289_ = lean_box(0);
            v___x_7290_ = lean_apply_1(v_h__2_7279_, v___x_7289_);
            return v___x_7290_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(
    mut v_motive_7291_: *mut LeanObject,
    mut v_k_7292_: *mut LeanObject,
    mut v_h__1_7293_: *mut LeanObject,
    mut v_h__2_7294_: *mut LeanObject,
    mut v_h__3_7295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7296_: *mut LeanObject = core::ptr::null_mut();
    v_res_7296_ =
        l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(
            v_motive_7291_,
            v_k_7292_,
            v_h__1_7293_,
            v_h__2_7294_,
            v_h__3_7295_,
        );
    lean_dec(v_k_7292_);
    return v_res_7296_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(
    mut v_x_7297_: *mut LeanObject,
    mut v_h__1_7298_: *mut LeanObject,
    mut v_h__2_7299_: *mut LeanObject,
    mut v_h__3_7300_: *mut LeanObject,
    mut v_h__4_7301_: *mut LeanObject,
    mut v_h__5_7302_: *mut LeanObject,
    mut v_h__6_7303_: *mut LeanObject,
    mut v_h__7_7304_: *mut LeanObject,
    mut v_h__8_7305_: *mut LeanObject,
    mut v_h__9_7306_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_7297_) {
        0 => {
            let mut v_k_7307_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7308_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            v_k_7307_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc(v_k_7307_);
            lean_dec_ref_known(v_x_7297_, 1);
            v___x_7308_ = lean_apply_1(v_h__1_7298_, v_k_7307_);
            return v___x_7308_;
        }
        1 => {
            let mut v_k_7309_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__1_7298_);
            v_k_7309_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc(v_k_7309_);
            lean_dec_ref_known(v_x_7297_, 1);
            v___x_7310_ = lean_apply_1(v_h__2_7299_, v_k_7309_);
            return v___x_7310_;
        }
        2 => {
            let mut v_k_7311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_k_7311_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc(v_k_7311_);
            lean_dec_ref_known(v_x_7297_, 1);
            v___x_7312_ = lean_apply_1(v_h__3_7300_, v_k_7311_);
            return v___x_7312_;
        }
        3 => {
            let mut v_i_7313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_i_7313_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc(v_i_7313_);
            lean_dec_ref_known(v_x_7297_, 1);
            v___x_7314_ = lean_apply_1(v_h__4_7301_, v_i_7313_);
            return v___x_7314_;
        }
        4 => {
            let mut v_a_7315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_a_7315_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc_ref(v_a_7315_);
            lean_dec_ref_known(v_x_7297_, 1);
            v___x_7316_ = lean_apply_1(v_h__7_7304_, v_a_7315_);
            return v___x_7316_;
        }
        5 => {
            let mut v_a_7317_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_7318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_a_7317_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc_ref(v_a_7317_);
            v_b_7318_ = lean_ctor_get(v_x_7297_, 1);
            lean_inc_ref(v_b_7318_);
            lean_dec_ref_known(v_x_7297_, 2);
            v___x_7319_ = lean_apply_2(v_h__5_7302_, v_a_7317_, v_b_7318_);
            return v___x_7319_;
        }
        6 => {
            let mut v_a_7320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_7321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_a_7320_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc_ref(v_a_7320_);
            v_b_7321_ = lean_ctor_get(v_x_7297_, 1);
            lean_inc_ref(v_b_7321_);
            lean_dec_ref_known(v_x_7297_, 2);
            v___x_7322_ = lean_apply_2(v_h__8_7305_, v_a_7320_, v_b_7321_);
            return v___x_7322_;
        }
        7 => {
            let mut v_a_7323_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_7324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7306_);
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_a_7323_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc_ref(v_a_7323_);
            v_b_7324_ = lean_ctor_get(v_x_7297_, 1);
            lean_inc_ref(v_b_7324_);
            lean_dec_ref_known(v_x_7297_, 2);
            v___x_7325_ = lean_apply_2(v_h__6_7303_, v_a_7323_, v_b_7324_);
            return v___x_7325_;
        }
        _ => {
            let mut v_a_7326_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_7327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_7305_);
            lean_dec(v_h__7_7304_);
            lean_dec(v_h__6_7303_);
            lean_dec(v_h__5_7302_);
            lean_dec(v_h__4_7301_);
            lean_dec(v_h__3_7300_);
            lean_dec(v_h__2_7299_);
            lean_dec(v_h__1_7298_);
            v_a_7326_ = lean_ctor_get(v_x_7297_, 0);
            lean_inc_ref(v_a_7326_);
            v_k_7327_ = lean_ctor_get(v_x_7297_, 1);
            lean_inc(v_k_7327_);
            lean_dec_ref_known(v_x_7297_, 2);
            v___x_7328_ = lean_apply_2(v_h__9_7306_, v_a_7326_, v_k_7327_);
            return v___x_7328_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(
    mut v_motive_7329_: *mut LeanObject,
    mut v_x_7330_: *mut LeanObject,
    mut v_h__1_7331_: *mut LeanObject,
    mut v_h__2_7332_: *mut LeanObject,
    mut v_h__3_7333_: *mut LeanObject,
    mut v_h__4_7334_: *mut LeanObject,
    mut v_h__5_7335_: *mut LeanObject,
    mut v_h__6_7336_: *mut LeanObject,
    mut v_h__7_7337_: *mut LeanObject,
    mut v_h__8_7338_: *mut LeanObject,
    mut v_h__9_7339_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_7330_) {
        0 => {
            let mut v_k_7340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            v_k_7340_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc(v_k_7340_);
            lean_dec_ref_known(v_x_7330_, 1);
            v___x_7341_ = lean_apply_1(v_h__1_7331_, v_k_7340_);
            return v___x_7341_;
        }
        1 => {
            let mut v_k_7342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__1_7331_);
            v_k_7342_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc(v_k_7342_);
            lean_dec_ref_known(v_x_7330_, 1);
            v___x_7343_ = lean_apply_1(v_h__2_7332_, v_k_7342_);
            return v___x_7343_;
        }
        2 => {
            let mut v_k_7344_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_k_7344_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc(v_k_7344_);
            lean_dec_ref_known(v_x_7330_, 1);
            v___x_7345_ = lean_apply_1(v_h__3_7333_, v_k_7344_);
            return v___x_7345_;
        }
        3 => {
            let mut v_i_7346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7347_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_i_7346_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc(v_i_7346_);
            lean_dec_ref_known(v_x_7330_, 1);
            v___x_7347_ = lean_apply_1(v_h__4_7334_, v_i_7346_);
            return v___x_7347_;
        }
        4 => {
            let mut v_a_7348_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_a_7348_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc_ref(v_a_7348_);
            lean_dec_ref_known(v_x_7330_, 1);
            v___x_7349_ = lean_apply_1(v_h__7_7337_, v_a_7348_);
            return v___x_7349_;
        }
        5 => {
            let mut v_a_7350_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_7351_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_a_7350_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc_ref(v_a_7350_);
            v_b_7351_ = lean_ctor_get(v_x_7330_, 1);
            lean_inc_ref(v_b_7351_);
            lean_dec_ref_known(v_x_7330_, 2);
            v___x_7352_ = lean_apply_2(v_h__5_7335_, v_a_7350_, v_b_7351_);
            return v___x_7352_;
        }
        6 => {
            let mut v_a_7353_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_7354_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_a_7353_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc_ref(v_a_7353_);
            v_b_7354_ = lean_ctor_get(v_x_7330_, 1);
            lean_inc_ref(v_b_7354_);
            lean_dec_ref_known(v_x_7330_, 2);
            v___x_7355_ = lean_apply_2(v_h__8_7338_, v_a_7353_, v_b_7354_);
            return v___x_7355_;
        }
        7 => {
            let mut v_a_7356_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_7357_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_7339_);
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_a_7356_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc_ref(v_a_7356_);
            v_b_7357_ = lean_ctor_get(v_x_7330_, 1);
            lean_inc_ref(v_b_7357_);
            lean_dec_ref_known(v_x_7330_, 2);
            v___x_7358_ = lean_apply_2(v_h__6_7336_, v_a_7356_, v_b_7357_);
            return v___x_7358_;
        }
        _ => {
            let mut v_a_7359_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_7360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_7338_);
            lean_dec(v_h__7_7337_);
            lean_dec(v_h__6_7336_);
            lean_dec(v_h__5_7335_);
            lean_dec(v_h__4_7334_);
            lean_dec(v_h__3_7333_);
            lean_dec(v_h__2_7332_);
            lean_dec(v_h__1_7331_);
            v_a_7359_ = lean_ctor_get(v_x_7330_, 0);
            lean_inc_ref(v_a_7359_);
            v_k_7360_ = lean_ctor_get(v_x_7330_, 1);
            lean_inc(v_k_7360_);
            lean_dec_ref_known(v_x_7330_, 2);
            v___x_7361_ = lean_apply_2(v_h__9_7339_, v_a_7359_, v_k_7360_);
            return v___x_7361_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(
    mut v_a_7362_: *mut LeanObject,
    mut v_h__1_7363_: *mut LeanObject,
    mut v_h__2_7364_: *mut LeanObject,
    mut v_h__3_7365_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_7362_) {
        0 => {
            let mut v_k_7366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7365_);
            lean_dec(v_h__2_7364_);
            v_k_7366_ = lean_ctor_get(v_a_7362_, 0);
            lean_inc(v_k_7366_);
            lean_dec_ref_known(v_a_7362_, 1);
            v___x_7367_ = lean_apply_1(v_h__1_7363_, v_k_7366_);
            return v___x_7367_;
        }
        3 => {
            let mut v_i_7368_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7365_);
            lean_dec(v_h__1_7363_);
            v_i_7368_ = lean_ctor_get(v_a_7362_, 0);
            lean_inc(v_i_7368_);
            lean_dec_ref_known(v_a_7362_, 1);
            v___x_7369_ = lean_apply_1(v_h__2_7364_, v_i_7368_);
            return v___x_7369_;
        }
        _ => {
            let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_7364_);
            lean_dec(v_h__1_7363_);
            v___x_7370_ = lean_apply_3(v_h__3_7365_, v_a_7362_, lean_box(0), lean_box(0));
            return v___x_7370_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(
    mut v_motive_7371_: *mut LeanObject,
    mut v_a_7372_: *mut LeanObject,
    mut v_h__1_7373_: *mut LeanObject,
    mut v_h__2_7374_: *mut LeanObject,
    mut v_h__3_7375_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_7372_) {
        0 => {
            let mut v_k_7376_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7375_);
            lean_dec(v_h__2_7374_);
            v_k_7376_ = lean_ctor_get(v_a_7372_, 0);
            lean_inc(v_k_7376_);
            lean_dec_ref_known(v_a_7372_, 1);
            v___x_7377_ = lean_apply_1(v_h__1_7373_, v_k_7376_);
            return v___x_7377_;
        }
        3 => {
            let mut v_i_7378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_7375_);
            lean_dec(v_h__1_7373_);
            v_i_7378_ = lean_ctor_get(v_a_7372_, 0);
            lean_inc(v_i_7378_);
            lean_dec_ref_known(v_a_7372_, 1);
            v___x_7379_ = lean_apply_1(v_h__2_7374_, v_i_7378_);
            return v___x_7379_;
        }
        _ => {
            let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_7374_);
            lean_dec(v_h__1_7373_);
            v___x_7380_ = lean_apply_3(v_h__3_7375_, v_a_7372_, lean_box(0), lean_box(0));
            return v___x_7380_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
    mut v_inst_7381_: *mut LeanObject,
    mut v_ctx_7382_: *mut LeanObject,
    mut v_m_7383_: *mut LeanObject,
    mut v_acc_7384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMul_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNat_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: u8 = 0;
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: u8 = 0;
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_7383_) == 0 {
                    lean_dec_ref(v_inst_7381_);
                    return v_acc_7384_;
                } else {
                    v_toSemiring_7385_ = lean_ctor_get(v_inst_7381_, 0);
                    v_toMul_7386_ = lean_ctor_get(v_toSemiring_7385_, 1);
                    v_ofNat_7387_ = lean_ctor_get(v_toSemiring_7385_, 3);
                    v_npow_7388_ = lean_ctor_get(v_toSemiring_7385_, 5);
                    v_p_7389_ = lean_ctor_get(v_m_7383_, 0);
                    lean_inc_ref(v_p_7389_);
                    v_m_7390_ = lean_ctor_get(v_m_7383_, 1);
                    lean_inc(v_m_7390_);
                    lean_dec_ref_known(v_m_7383_, 2);
                    v_x_7395_ = lean_ctor_get(v_p_7389_, 0);
                    lean_inc(v_x_7395_);
                    v_k_7396_ = lean_ctor_get(v_p_7389_, 1);
                    lean_inc(v_k_7396_);
                    lean_dec_ref(v_p_7389_);
                    v___x_7397_ = lean_unsigned_to_nat(0);
                    v___x_7398_ = lean_nat_dec_eq(v_k_7396_, v___x_7397_);
                    if v___x_7398_ == 0 {
                        v___x_7399_ = lean_unsigned_to_nat(1);
                        v___x_7400_ = lean_nat_dec_eq(v_k_7396_, v___x_7399_);
                        if v___x_7400_ == 0 {
                            v___x_7401_ = l_Lean_RArray_getImpl___redArg(v_ctx_7382_, v_x_7395_);
                            lean_dec(v_x_7395_);
                            lean_inc(v_npow_7388_);
                            v___x_7402_ = lean_apply_2(v_npow_7388_, v___x_7401_, v_k_7396_);
                            v___y_7392_ = v___x_7402_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_k_7396_);
                            v___x_7403_ = l_Lean_RArray_getImpl___redArg(v_ctx_7382_, v_x_7395_);
                            lean_dec(v_x_7395_);
                            v___y_7392_ = v___x_7403_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_7396_);
                        lean_dec(v_x_7395_);
                        v___x_7404_ = lean_unsigned_to_nat(1);
                        lean_inc(v_ofNat_7387_);
                        v___x_7405_ = lean_apply_1(v_ofNat_7387_, v___x_7404_);
                        v___y_7392_ = v___x_7405_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_toMul_7386_);
                v___x_7393_ = lean_apply_2(v_toMul_7386_, v_acc_7384_, v___y_7392_);
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
    mut v_inst_7406_: *mut LeanObject,
    mut v_ctx_7407_: *mut LeanObject,
    mut v_m_7408_: *mut LeanObject,
    mut v_acc_7409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7410_: *mut LeanObject = core::ptr::null_mut();
    v_res_7410_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
        v_inst_7406_,
        v_ctx_7407_,
        v_m_7408_,
        v_acc_7409_,
    );
    lean_dec_ref(v_ctx_7407_);
    return v_res_7410_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(
    mut v_00_u03b1_7411_: *mut LeanObject,
    mut v_inst_7412_: *mut LeanObject,
    mut v_ctx_7413_: *mut LeanObject,
    mut v_m_7414_: *mut LeanObject,
    mut v_acc_7415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7416_: *mut LeanObject = core::ptr::null_mut();
    v___x_7416_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
        v_inst_7412_,
        v_ctx_7413_,
        v_m_7414_,
        v_acc_7415_,
    );
    return v___x_7416_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(
    mut v_00_u03b1_7417_: *mut LeanObject,
    mut v_inst_7418_: *mut LeanObject,
    mut v_ctx_7419_: *mut LeanObject,
    mut v_m_7420_: *mut LeanObject,
    mut v_acc_7421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7422_: *mut LeanObject = core::ptr::null_mut();
    v_res_7422_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(
        v_00_u03b1_7417_,
        v_inst_7418_,
        v_ctx_7419_,
        v_m_7420_,
        v_acc_7421_,
    );
    lean_dec_ref(v_ctx_7419_);
    return v_res_7422_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(
    mut v_inst_7423_: *mut LeanObject,
    mut v_ctx_7424_: *mut LeanObject,
    mut v_m_7425_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_7425_) == 0 {
        let mut v_toSemiring_7426_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_7427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7429_: *mut LeanObject = core::ptr::null_mut();
        v_toSemiring_7426_ = lean_ctor_get(v_inst_7423_, 0);
        lean_inc_ref(v_toSemiring_7426_);
        lean_dec_ref(v_inst_7423_);
        v_ofNat_7427_ = lean_ctor_get(v_toSemiring_7426_, 3);
        lean_inc(v_ofNat_7427_);
        lean_dec_ref(v_toSemiring_7426_);
        v___x_7428_ = lean_unsigned_to_nat(1);
        v___x_7429_ = lean_apply_1(v_ofNat_7427_, v___x_7428_);
        return v___x_7429_;
    } else {
        let mut v_toSemiring_7430_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_7431_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_7432_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_7433_: *mut LeanObject = core::ptr::null_mut();
        let mut v_npow_7434_: *mut LeanObject = core::ptr::null_mut();
        let mut v_x_7435_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_7436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7438_: u8 = 0;
        v_toSemiring_7430_ = lean_ctor_get(v_inst_7423_, 0);
        v_p_7431_ = lean_ctor_get(v_m_7425_, 0);
        lean_inc_ref(v_p_7431_);
        v_m_7432_ = lean_ctor_get(v_m_7425_, 1);
        lean_inc(v_m_7432_);
        lean_dec_ref_known(v_m_7425_, 2);
        v_ofNat_7433_ = lean_ctor_get(v_toSemiring_7430_, 3);
        v_npow_7434_ = lean_ctor_get(v_toSemiring_7430_, 5);
        v_x_7435_ = lean_ctor_get(v_p_7431_, 0);
        lean_inc(v_x_7435_);
        v_k_7436_ = lean_ctor_get(v_p_7431_, 1);
        lean_inc(v_k_7436_);
        lean_dec_ref(v_p_7431_);
        v___x_7437_ = lean_unsigned_to_nat(0);
        v___x_7438_ = lean_nat_dec_eq(v_k_7436_, v___x_7437_);
        if v___x_7438_ == 0 {
            let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7440_: u8 = 0;
            v___x_7439_ = lean_unsigned_to_nat(1);
            v___x_7440_ = lean_nat_dec_eq(v_k_7436_, v___x_7439_);
            if v___x_7440_ == 0 {
                let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7443_: *mut LeanObject = core::ptr::null_mut();
                v___x_7441_ = l_Lean_RArray_getImpl___redArg(v_ctx_7424_, v_x_7435_);
                lean_dec(v_x_7435_);
                lean_inc(v_npow_7434_);
                v___x_7442_ = lean_apply_2(v_npow_7434_, v___x_7441_, v_k_7436_);
                v___x_7443_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
                    v_inst_7423_,
                    v_ctx_7424_,
                    v_m_7432_,
                    v___x_7442_,
                );
                return v___x_7443_;
            } else {
                let mut v___x_7444_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_k_7436_);
                v___x_7444_ = l_Lean_RArray_getImpl___redArg(v_ctx_7424_, v_x_7435_);
                lean_dec(v_x_7435_);
                v___x_7445_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(
                    v_inst_7423_,
                    v_ctx_7424_,
                    v_m_7432_,
                    v___x_7444_,
                );
                return v___x_7445_;
            }
        } else {
            let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7448_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_7436_);
            lean_dec(v_x_7435_);
            v___x_7446_ = lean_unsigned_to_nat(1);
            lean_inc(v_ofNat_7433_);
            v___x_7447_ = lean_apply_1(v_ofNat_7433_, v___x_7446_);
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
    mut v_inst_7449_: *mut LeanObject,
    mut v_ctx_7450_: *mut LeanObject,
    mut v_m_7451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7452_: *mut LeanObject = core::ptr::null_mut();
    v_res_7452_ =
        l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_7449_, v_ctx_7450_, v_m_7451_);
    lean_dec_ref(v_ctx_7450_);
    return v_res_7452_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule(
    mut v_00_u03b1_7453_: *mut LeanObject,
    mut v_inst_7454_: *mut LeanObject,
    mut v_ctx_7455_: *mut LeanObject,
    mut v_m_7456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    v___x_7457_ =
        l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_7454_, v_ctx_7455_, v_m_7456_);
    return v___x_7457_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(
    mut v_00_u03b1_7458_: *mut LeanObject,
    mut v_inst_7459_: *mut LeanObject,
    mut v_ctx_7460_: *mut LeanObject,
    mut v_m_7461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7462_: *mut LeanObject = core::ptr::null_mut();
    v_res_7462_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(
        v_00_u03b1_7458_,
        v_inst_7459_,
        v_ctx_7460_,
        v_m_7461_,
    );
    lean_dec_ref(v_ctx_7460_);
    return v_res_7462_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(
    mut v_inst_7463_: *mut LeanObject,
    mut v_ctx_7464_: *mut LeanObject,
    mut v_p_7465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_7463_);
    v___x_7466_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_7463_);
    if lean_obj_tag(v_p_7465_) == 0 {
        let mut v_toSemiring_7467_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zsmul_7468_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_7469_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_7470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
        v_toSemiring_7467_ = lean_ctor_get(v_inst_7463_, 0);
        lean_inc_ref(v_toSemiring_7467_);
        lean_dec_ref(v_inst_7463_);
        v_zsmul_7468_ = lean_ctor_get(v___x_7466_, 2);
        lean_inc(v_zsmul_7468_);
        lean_dec_ref(v___x_7466_);
        v_ofNat_7469_ = lean_ctor_get(v_toSemiring_7467_, 3);
        lean_inc(v_ofNat_7469_);
        lean_dec_ref(v_toSemiring_7467_);
        v_k_7470_ = lean_ctor_get(v_p_7465_, 0);
        lean_inc(v_k_7470_);
        lean_dec_ref_known(v_p_7465_, 1);
        v___x_7471_ = lean_unsigned_to_nat(1);
        v___x_7472_ = lean_apply_1(v_ofNat_7469_, v___x_7471_);
        v___x_7473_ = lean_apply_2(v_zsmul_7468_, v_k_7470_, v___x_7472_);
        return v___x_7473_;
    } else {
        let mut v_toSemiring_7474_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zsmul_7475_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toAdd_7476_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_7477_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_7478_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_7479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
        v_toSemiring_7474_ = lean_ctor_get(v_inst_7463_, 0);
        v_zsmul_7475_ = lean_ctor_get(v___x_7466_, 2);
        lean_inc(v_zsmul_7475_);
        lean_dec_ref(v___x_7466_);
        v_toAdd_7476_ = lean_ctor_get(v_toSemiring_7474_, 0);
        lean_inc(v_toAdd_7476_);
        v_k_7477_ = lean_ctor_get(v_p_7465_, 0);
        lean_inc(v_k_7477_);
        v_v_7478_ = lean_ctor_get(v_p_7465_, 1);
        lean_inc(v_v_7478_);
        v_p_7479_ = lean_ctor_get(v_p_7465_, 2);
        lean_inc_ref(v_p_7479_);
        lean_dec_ref_known(v_p_7465_, 3);
        lean_inc_ref(v_inst_7463_);
        v___x_7480_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(
            v_inst_7463_,
            v_ctx_7464_,
            v_v_7478_,
        );
        v___x_7481_ = lean_apply_2(v_zsmul_7475_, v_k_7477_, v___x_7480_);
        v___x_7482_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(
            v_inst_7463_,
            v_ctx_7464_,
            v_p_7479_,
        );
        v___x_7483_ = lean_apply_2(v_toAdd_7476_, v___x_7481_, v___x_7482_);
        return v___x_7483_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(
    mut v_inst_7484_: *mut LeanObject,
    mut v_ctx_7485_: *mut LeanObject,
    mut v_p_7486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7487_: *mut LeanObject = core::ptr::null_mut();
    v_res_7487_ =
        l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_7484_, v_ctx_7485_, v_p_7486_);
    lean_dec_ref(v_ctx_7485_);
    return v_res_7487_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule(
    mut v_00_u03b1_7488_: *mut LeanObject,
    mut v_inst_7489_: *mut LeanObject,
    mut v_ctx_7490_: *mut LeanObject,
    mut v_p_7491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7492_: *mut LeanObject = core::ptr::null_mut();
    v___x_7492_ =
        l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_7489_, v_ctx_7490_, v_p_7491_);
    return v___x_7492_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(
    mut v_00_u03b1_7493_: *mut LeanObject,
    mut v_inst_7494_: *mut LeanObject,
    mut v_ctx_7495_: *mut LeanObject,
    mut v_p_7496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7497_: *mut LeanObject = core::ptr::null_mut();
    v_res_7497_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(
        v_00_u03b1_7493_,
        v_inst_7494_,
        v_ctx_7495_,
        v_p_7496_,
    );
    lean_dec_ref(v_ctx_7495_);
    return v_res_7497_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__gcd__cert(
    mut v_a_7498_: *mut LeanObject,
    mut v_b_7499_: *mut LeanObject,
    mut v_p_u2081_7500_: *mut LeanObject,
    mut v_p_u2082_7501_: *mut LeanObject,
    mut v_p_7502_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_p_u2081_7500_) == 0 {
        if lean_obj_tag(v_p_u2082_7501_) == 0 {
            if lean_obj_tag(v_p_7502_) == 0 {
                let mut v_k_7503_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_7504_: *mut LeanObject = core::ptr::null_mut();
                let mut v_k_7505_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7506_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7507_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7508_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7509_: u8 = 0;
                v_k_7503_ = lean_ctor_get(v_p_u2081_7500_, 0);
                v_k_7504_ = lean_ctor_get(v_p_u2082_7501_, 0);
                v_k_7505_ = lean_ctor_get(v_p_7502_, 0);
                v___x_7506_ = lean_int_mul(v_a_7498_, v_k_7503_);
                v___x_7507_ = lean_int_mul(v_b_7499_, v_k_7504_);
                v___x_7508_ = lean_int_add(v___x_7506_, v___x_7507_);
                lean_dec(v___x_7507_);
                lean_dec(v___x_7506_);
                v___x_7509_ = lean_int_dec_eq(v_k_7505_, v___x_7508_);
                lean_dec(v___x_7508_);
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
    mut v_a_7513_: *mut LeanObject,
    mut v_b_7514_: *mut LeanObject,
    mut v_p_u2081_7515_: *mut LeanObject,
    mut v_p_u2082_7516_: *mut LeanObject,
    mut v_p_7517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7518_: u8 = 0;
    let mut v_r_7519_: *mut LeanObject = core::ptr::null_mut();
    v_res_7518_ = l_Lean_Grind_CommRing_eq__gcd__cert(
        v_a_7513_,
        v_b_7514_,
        v_p_u2081_7515_,
        v_p_u2082_7516_,
        v_p_7517_,
    );
    lean_dec_ref(v_p_7517_);
    lean_dec_ref(v_p_u2082_7516_);
    lean_dec_ref(v_p_u2081_7515_);
    lean_dec(v_b_7514_);
    lean_dec(v_a_7513_);
    v_r_7519_ = lean_box((v_res_7518_) as usize);
    return v_r_7519_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(
    mut v_p_7520_: *mut LeanObject,
    mut v_h__1_7521_: *mut LeanObject,
    mut v_h__2_7522_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_7520_) == 0 {
        let mut v_k_7523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_7521_);
        v_k_7523_ = lean_ctor_get(v_p_7520_, 0);
        lean_inc(v_k_7523_);
        lean_dec_ref_known(v_p_7520_, 1);
        v___x_7524_ = lean_apply_1(v_h__2_7522_, v_k_7523_);
        return v___x_7524_;
    } else {
        let mut v_k_7525_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_7526_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_7527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_7522_);
        v_k_7525_ = lean_ctor_get(v_p_7520_, 0);
        lean_inc(v_k_7525_);
        v_v_7526_ = lean_ctor_get(v_p_7520_, 1);
        lean_inc(v_v_7526_);
        v_p_7527_ = lean_ctor_get(v_p_7520_, 2);
        lean_inc_ref(v_p_7527_);
        lean_dec_ref_known(v_p_7520_, 3);
        v___x_7528_ = lean_apply_3(v_h__1_7521_, v_k_7525_, v_v_7526_, v_p_7527_);
        return v___x_7528_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(
    mut v_motive_7529_: *mut LeanObject,
    mut v_p_7530_: *mut LeanObject,
    mut v_h__1_7531_: *mut LeanObject,
    mut v_h__2_7532_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_7530_) == 0 {
        let mut v_k_7533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_7531_);
        v_k_7533_ = lean_ctor_get(v_p_7530_, 0);
        lean_inc(v_k_7533_);
        lean_dec_ref_known(v_p_7530_, 1);
        v___x_7534_ = lean_apply_1(v_h__2_7532_, v_k_7533_);
        return v___x_7534_;
    } else {
        let mut v_k_7535_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_7536_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_7537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_7532_);
        v_k_7535_ = lean_ctor_get(v_p_7530_, 0);
        lean_inc(v_k_7535_);
        v_v_7536_ = lean_ctor_get(v_p_7530_, 1);
        lean_inc(v_v_7536_);
        v_p_7537_ = lean_ctor_get(v_p_7530_, 2);
        lean_inc_ref(v_p_7537_);
        lean_dec_ref_known(v_p_7530_, 3);
        v___x_7538_ = lean_apply_3(v_h__1_7531_, v_k_7535_, v_v_7536_, v_p_7537_);
        return v___x_7538_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_CommSolver(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Field(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ordered_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Grind_CommRing_instInhabitedExpr_default =
        _init_l_Lean_Grind_CommRing_instInhabitedExpr_default();
    lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr_default);
    l_Lean_Grind_CommRing_instInhabitedExpr = _init_l_Lean_Grind_CommRing_instInhabitedExpr();
    lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr);
    l_Lean_Grind_CommRing_instInhabitedMon_default =
        _init_l_Lean_Grind_CommRing_instInhabitedMon_default();
    lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon_default);
    l_Lean_Grind_CommRing_instInhabitedMon = _init_l_Lean_Grind_CommRing_instInhabitedMon();
    lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon);
    l_Lean_Grind_CommRing_hugeFuel = _init_l_Lean_Grind_CommRing_hugeFuel();
    lean_mark_persistent(l_Lean_Grind_CommRing_hugeFuel);
    l_Lean_Grind_CommRing_instInhabitedPoly_default =
        _init_l_Lean_Grind_CommRing_instInhabitedPoly_default();
    lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly_default);
    l_Lean_Grind_CommRing_instInhabitedPoly = _init_l_Lean_Grind_CommRing_instInhabitedPoly();
    lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ring_CommSolver(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Ring_CommSolver(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Field(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ordered_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_CommSolver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Ring_CommSolver(builtin);
}
