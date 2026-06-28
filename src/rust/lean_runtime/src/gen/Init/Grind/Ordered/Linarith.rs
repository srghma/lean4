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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_apply_6, lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Lean_Grind_Linarith_instInhabitedExpr_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_Linarith_instInhabitedExpr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_instBEqExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_Linarith_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Linarith_instBEqExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_Linarith_instBEqExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 122, 101, 114, 111, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value: LeanStringObject<29> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value: LeanStringObject<29> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value: LeanStringObject<29> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__12_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value: LeanStringObject<29> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__15_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 110, 97, 116, 77, 117, 108, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__18_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 69, 120, 112, 114, 46, 105, 110, 116, 77, 117, 108, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprExpr_repr___closed__21_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Linarith_instReprExpr_repr___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_instReprExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_Linarith_instReprExpr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Linarith_instReprExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_Linarith_instReprExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instBEqPoly___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_Linarith_instBEqPoly_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Linarith_instBEqPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqPoly___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_Linarith_instBEqPoly: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instBEqPoly___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value: LeanStringObject<29> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 80, 111, 108, 121, 46, 110, 105, 108, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value: LeanStringObject<29> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104,
            46, 80, 111, 108, 121, 46, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly_repr___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_Linarith_instReprPoly_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_Linarith_instReprPoly___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_Linarith_instReprPoly_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Linarith_instReprPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_Linarith_instReprPoly: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_instReprPoly___closed__0_value) as *mut LeanObject;
static mut l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Linarith_diseq__split__cert___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorIdx(
    mut v_x_1245_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1245_) {
        0 => {
            let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
            v___x_1246_ = lean_unsigned_to_nat(0);
            return v___x_1246_;
        }
        1 => {
            let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
            v___x_1247_ = lean_unsigned_to_nat(1);
            return v___x_1247_;
        }
        2 => {
            let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
            v___x_1248_ = lean_unsigned_to_nat(2);
            return v___x_1248_;
        }
        3 => {
            let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
            v___x_1249_ = lean_unsigned_to_nat(3);
            return v___x_1249_;
        }
        4 => {
            let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
            v___x_1250_ = lean_unsigned_to_nat(4);
            return v___x_1250_;
        }
        5 => {
            let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
            v___x_1251_ = lean_unsigned_to_nat(5);
            return v___x_1251_;
        }
        _ => {
            let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
            v___x_1252_ = lean_unsigned_to_nat(6);
            return v___x_1252_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorIdx___boxed(
    mut v_x_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1254_: *mut LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lean_Grind_Linarith_Expr_ctorIdx(v_x_1253_);
    lean_dec(v_x_1253_);
    return v_res_1254_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorElim___redArg(
    mut v_t_1255_: *mut LeanObject,
    mut v_k_1256_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1255_) {
        0 => {
            return v_k_1256_;
        }
        1 => {
            let mut v_i_1257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
            v_i_1257_ = lean_ctor_get(v_t_1255_, 0);
            lean_inc(v_i_1257_);
            lean_dec_ref_known(v_t_1255_, 1);
            v___x_1258_ = lean_apply_1(v_k_1256_, v_i_1257_);
            return v___x_1258_;
        }
        4 => {
            let mut v_a_1259_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
            v_a_1259_ = lean_ctor_get(v_t_1255_, 0);
            lean_inc(v_a_1259_);
            lean_dec_ref_known(v_t_1255_, 1);
            v___x_1260_ = lean_apply_1(v_k_1256_, v_a_1259_);
            return v___x_1260_;
        }
        _ => {
            let mut v_a_1261_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1262_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
            v_a_1261_ = lean_ctor_get(v_t_1255_, 0);
            lean_inc(v_a_1261_);
            v_b_1262_ = lean_ctor_get(v_t_1255_, 1);
            lean_inc(v_b_1262_);
            lean_dec(v_t_1255_);
            v___x_1263_ = lean_apply_2(v_k_1256_, v_a_1261_, v_b_1262_);
            return v___x_1263_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorElim(
    mut v_motive_1264_: *mut LeanObject,
    mut v_ctorIdx_1265_: *mut LeanObject,
    mut v_t_1266_: *mut LeanObject,
    mut v_h_1267_: *mut LeanObject,
    mut v_k_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1266_, v_k_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_ctorElim___boxed(
    mut v_motive_1270_: *mut LeanObject,
    mut v_ctorIdx_1271_: *mut LeanObject,
    mut v_t_1272_: *mut LeanObject,
    mut v_h_1273_: *mut LeanObject,
    mut v_k_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1275_: *mut LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_Grind_Linarith_Expr_ctorElim(
        v_motive_1270_,
        v_ctorIdx_1271_,
        v_t_1272_,
        v_h_1273_,
        v_k_1274_,
    );
    lean_dec(v_ctorIdx_1271_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_zero_elim___redArg(
    mut v_t_1276_: *mut LeanObject,
    mut v_zero_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1276_, v_zero_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_zero_elim(
    mut v_motive_1279_: *mut LeanObject,
    mut v_t_1280_: *mut LeanObject,
    mut v_h_1281_: *mut LeanObject,
    mut v_zero_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1280_, v_zero_1282_);
    return v___x_1283_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_var_elim___redArg(
    mut v_t_1284_: *mut LeanObject,
    mut v_var_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    v___x_1286_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1284_, v_var_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_var_elim(
    mut v_motive_1287_: *mut LeanObject,
    mut v_t_1288_: *mut LeanObject,
    mut v_h_1289_: *mut LeanObject,
    mut v_var_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1288_, v_var_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_add_elim___redArg(
    mut v_t_1292_: *mut LeanObject,
    mut v_add_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1292_, v_add_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_add_elim(
    mut v_motive_1295_: *mut LeanObject,
    mut v_t_1296_: *mut LeanObject,
    mut v_h_1297_: *mut LeanObject,
    mut v_add_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1296_, v_add_1298_);
    return v___x_1299_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_sub_elim___redArg(
    mut v_t_1300_: *mut LeanObject,
    mut v_sub_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1300_, v_sub_1301_);
    return v___x_1302_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_sub_elim(
    mut v_motive_1303_: *mut LeanObject,
    mut v_t_1304_: *mut LeanObject,
    mut v_h_1305_: *mut LeanObject,
    mut v_sub_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1304_, v_sub_1306_);
    return v___x_1307_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_neg_elim___redArg(
    mut v_t_1308_: *mut LeanObject,
    mut v_neg_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    v___x_1310_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1308_, v_neg_1309_);
    return v___x_1310_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_neg_elim(
    mut v_motive_1311_: *mut LeanObject,
    mut v_t_1312_: *mut LeanObject,
    mut v_h_1313_: *mut LeanObject,
    mut v_neg_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1312_, v_neg_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_natMul_elim___redArg(
    mut v_t_1316_: *mut LeanObject,
    mut v_natMul_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    v___x_1318_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1316_, v_natMul_1317_);
    return v___x_1318_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_natMul_elim(
    mut v_motive_1319_: *mut LeanObject,
    mut v_t_1320_: *mut LeanObject,
    mut v_h_1321_: *mut LeanObject,
    mut v_natMul_1322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v___x_1323_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1320_, v_natMul_1322_);
    return v___x_1323_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_intMul_elim___redArg(
    mut v_t_1324_: *mut LeanObject,
    mut v_intMul_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1324_, v_intMul_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_intMul_elim(
    mut v_motive_1327_: *mut LeanObject,
    mut v_t_1328_: *mut LeanObject,
    mut v_h_1329_: *mut LeanObject,
    mut v_intMul_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_1328_, v_intMul_1330_);
    return v___x_1331_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instInhabitedExpr_default() -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = lean_box(0);
    return v___x_1332_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instInhabitedExpr() -> *mut LeanObject {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    v___x_1333_ = lean_box(0);
    return v___x_1333_;
}
pub unsafe fn l_Lean_Grind_Linarith_instBEqExpr_beq(
    mut v_x_1334_: *mut LeanObject,
    mut v_x_1335_: *mut LeanObject,
) -> u8 {
    let mut v_a_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: u8 = 0;
    let mut v_i_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v_a_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut v_a_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v_a_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u8 = 0;
    let mut v_k_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: u8 = 0;
    let mut v___x_1369_: u8 = 0;
    let mut v_k_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1334_) {
                0 => {
                    if lean_obj_tag(v_x_1335_) == 0 {
                        v___x_1343_ = 1;
                        return v___x_1343_;
                    } else {
                        v___x_1344_ = 0;
                        return v___x_1344_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_x_1335_) == 1 {
                        v_i_1345_ = lean_ctor_get(v_x_1334_, 0);
                        v_i_1346_ = lean_ctor_get(v_x_1335_, 0);
                        v___x_1347_ = lean_nat_dec_eq(v_i_1345_, v_i_1346_);
                        return v___x_1347_;
                    } else {
                        v___x_1348_ = 0;
                        return v___x_1348_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_x_1335_) == 2 {
                        v_a_1349_ = lean_ctor_get(v_x_1334_, 0);
                        v_b_1350_ = lean_ctor_get(v_x_1334_, 1);
                        v_a_1351_ = lean_ctor_get(v_x_1335_, 0);
                        v_b_1352_ = lean_ctor_get(v_x_1335_, 1);
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
                    if lean_obj_tag(v_x_1335_) == 3 {
                        v_a_1354_ = lean_ctor_get(v_x_1334_, 0);
                        v_b_1355_ = lean_ctor_get(v_x_1334_, 1);
                        v_a_1356_ = lean_ctor_get(v_x_1335_, 0);
                        v_b_1357_ = lean_ctor_get(v_x_1335_, 1);
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
                    if lean_obj_tag(v_x_1335_) == 4 {
                        v_a_1359_ = lean_ctor_get(v_x_1334_, 0);
                        v_a_1360_ = lean_ctor_get(v_x_1335_, 0);
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
                    if lean_obj_tag(v_x_1335_) == 5 {
                        v_k_1363_ = lean_ctor_get(v_x_1334_, 0);
                        v_a_1364_ = lean_ctor_get(v_x_1334_, 1);
                        v_k_1365_ = lean_ctor_get(v_x_1335_, 0);
                        v_a_1366_ = lean_ctor_get(v_x_1335_, 1);
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
                    if lean_obj_tag(v_x_1335_) == 6 {
                        v_k_1370_ = lean_ctor_get(v_x_1334_, 0);
                        v_a_1371_ = lean_ctor_get(v_x_1334_, 1);
                        v_k_1372_ = lean_ctor_get(v_x_1335_, 0);
                        v_a_1373_ = lean_ctor_get(v_x_1335_, 1);
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
    mut v_x_1377_: *mut LeanObject,
    mut v_x_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1379_: u8 = 0;
    let mut v_r_1380_: *mut LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_x_1377_, v_x_1378_);
    lean_dec(v_x_1378_);
    lean_dec(v_x_1377_);
    v_r_1380_ = lean_box((v_res_1379_) as usize);
    return v_r_1380_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2() -> *mut LeanObject {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1386_ = lean_unsigned_to_nat(2);
    v___x_1387_ = lean_nat_to_int(v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3() -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = lean_unsigned_to_nat(1);
    v___x_1389_ = lean_nat_to_int(v___x_1388_);
    return v___x_1389_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22() -> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_unsigned_to_nat(0);
    v___x_1427_ = lean_nat_to_int(v___x_1426_);
    return v___x_1427_;
}
pub unsafe fn l_Lean_Grind_Linarith_instReprExpr_repr(
    mut v_x_1428_: *mut LeanObject,
    mut v_prec_1429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: u8 = 0;
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___y_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_a_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_a_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut v_k_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1428_) {
                0 => {
                    v___x_1437_ = lean_unsigned_to_nat(1024);
                    v___x_1438_ = lean_nat_dec_le(v___x_1437_, v_prec_1429_);
                    if v___x_1438_ == 0 {
                        v___x_1439_ = lean_obj_once(
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
                        v___x_1440_ = lean_obj_once(
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
                    v_i_1441_ = lean_ctor_get(v_x_1428_, 0);
                    v_isSharedCheck_1461_ = (!lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1443_ = v_x_1428_;
                        v_isShared_1444_ = v_isSharedCheck_1461_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_i_1441_);
                        lean_dec(v_x_1428_);
                        v___x_1443_ = lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1461_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_a_1462_ = lean_ctor_get(v_x_1428_, 0);
                    v_b_1463_ = lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1486_ = (!lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1465_ = v_x_1428_;
                        v_isShared_1466_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_b_1463_);
                        lean_inc(v_a_1462_);
                        lean_dec(v_x_1428_);
                        v___x_1465_ = lean_box(0);
                        v_isShared_1466_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_a_1487_ = lean_ctor_get(v_x_1428_, 0);
                    v_b_1488_ = lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1511_ = (!lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1511_ == 0 {
                        v___x_1490_ = v_x_1428_;
                        v_isShared_1491_ = v_isSharedCheck_1511_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_b_1488_);
                        lean_inc(v_a_1487_);
                        lean_dec(v_x_1428_);
                        v___x_1490_ = lean_box(0);
                        v_isShared_1491_ = v_isSharedCheck_1511_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    v_a_1512_ = lean_ctor_get(v_x_1428_, 0);
                    lean_inc(v_a_1512_);
                    lean_dec_ref_known(v_x_1428_, 1);
                    v___x_1513_ = lean_unsigned_to_nat(1024);
                    v___x_1523_ = lean_nat_dec_le(v___x_1513_, v_prec_1429_);
                    if v___x_1523_ == 0 {
                        v___x_1524_ = lean_obj_once(
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
                        v___x_1525_ = lean_obj_once(
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
                    v_k_1526_ = lean_ctor_get(v_x_1428_, 0);
                    v_a_1527_ = lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1551_ = (!lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1551_ == 0 {
                        v___x_1529_ = v_x_1428_;
                        v_isShared_1530_ = v_isSharedCheck_1551_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1527_);
                        lean_inc(v_k_1526_);
                        lean_dec(v_x_1428_);
                        v___x_1529_ = lean_box(0);
                        v_isShared_1530_ = v_isSharedCheck_1551_;
                        state = 12;
                        continue;
                    }
                }
                _ => {
                    v_k_1552_ = lean_ctor_get(v_x_1428_, 0);
                    v_a_1553_ = lean_ctor_get(v_x_1428_, 1);
                    v_isSharedCheck_1587_ = (!lean_is_exclusive(v_x_1428_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1555_ = v_x_1428_;
                        v_isShared_1556_ = v_isSharedCheck_1587_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1553_);
                        lean_inc(v_k_1552_);
                        lean_dec(v_x_1428_);
                        v___x_1555_ = lean_box(0);
                        v_isShared_1556_ = v_isSharedCheck_1587_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1432_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__1;
                lean_inc(v___y_1431_);
                v___x_1433_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1433_, 0, v___y_1431_);
                lean_ctor_set(v___x_1433_, 1, v___x_1432_);
                v___x_1434_ = 0;
                v___x_1435_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1435_, 0, v___x_1433_);
                lean_ctor_set_uint8(
                    v___x_1435_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1434_,
                );
                v___x_1436_ = l_Repr_addAppParen(v___x_1435_, v_prec_1429_);
                return v___x_1436_;
            }
            2 => {
                v___x_1457_ = lean_unsigned_to_nat(1024);
                v___x_1458_ = lean_nat_dec_le(v___x_1457_, v_prec_1429_);
                if v___x_1458_ == 0 {
                    v___x_1459_ = lean_obj_once(
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
                    v___x_1460_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_1443_, 3);
                    lean_ctor_set(v___x_1443_, 0, v___x_1448_);
                    v___x_1450_ = v___x_1443_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1456_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1448_);
                    v___x_1450_ = v_reuseFailAlloc_1456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1451_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1451_, 0, v___x_1447_);
                lean_ctor_set(v___x_1451_, 1, v___x_1450_);
                lean_inc(v___y_1446_);
                v___x_1452_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1452_, 0, v___y_1446_);
                lean_ctor_set(v___x_1452_, 1, v___x_1451_);
                v___x_1453_ = 0;
                v___x_1454_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1454_, 0, v___x_1452_);
                lean_ctor_set_uint8(
                    v___x_1454_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1453_,
                );
                v___x_1455_ = l_Repr_addAppParen(v___x_1454_, v_prec_1429_);
                return v___x_1455_;
            }
            5 => {
                v___x_1467_ = lean_unsigned_to_nat(1024);
                v___x_1483_ = lean_nat_dec_le(v___x_1467_, v_prec_1429_);
                if v___x_1483_ == 0 {
                    v___x_1484_ = lean_obj_once(
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
                    v___x_1485_ = lean_obj_once(
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
                v___x_1470_ = lean_box(1);
                v___x_1471_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__9;
                v___x_1472_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1462_, v___x_1467_);
                if v_isShared_1466_ == 0 {
                    lean_ctor_set_tag(v___x_1465_, 5);
                    lean_ctor_set(v___x_1465_, 1, v___x_1472_);
                    lean_ctor_set(v___x_1465_, 0, v___x_1471_);
                    v___x_1474_ = v___x_1465_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1471_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1472_);
                    v___x_1474_ = v_reuseFailAlloc_1482_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1475_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                lean_ctor_set(v___x_1475_, 1, v___x_1470_);
                v___x_1476_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_1463_, v___x_1467_);
                v___x_1477_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1477_, 0, v___x_1475_);
                lean_ctor_set(v___x_1477_, 1, v___x_1476_);
                lean_inc(v___y_1469_);
                v___x_1478_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1478_, 0, v___y_1469_);
                lean_ctor_set(v___x_1478_, 1, v___x_1477_);
                v___x_1479_ = 0;
                v___x_1480_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1480_, 0, v___x_1478_);
                lean_ctor_set_uint8(
                    v___x_1480_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1479_,
                );
                v___x_1481_ = l_Repr_addAppParen(v___x_1480_, v_prec_1429_);
                return v___x_1481_;
            }
            8 => {
                v___x_1492_ = lean_unsigned_to_nat(1024);
                v___x_1508_ = lean_nat_dec_le(v___x_1492_, v_prec_1429_);
                if v___x_1508_ == 0 {
                    v___x_1509_ = lean_obj_once(
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
                    v___x_1510_ = lean_obj_once(
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
                v___x_1495_ = lean_box(1);
                v___x_1496_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__12;
                v___x_1497_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1487_, v___x_1492_);
                if v_isShared_1491_ == 0 {
                    lean_ctor_set_tag(v___x_1490_, 5);
                    lean_ctor_set(v___x_1490_, 1, v___x_1497_);
                    lean_ctor_set(v___x_1490_, 0, v___x_1496_);
                    v___x_1499_ = v___x_1490_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1496_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1497_);
                    v___x_1499_ = v_reuseFailAlloc_1507_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1500_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1500_, 0, v___x_1499_);
                lean_ctor_set(v___x_1500_, 1, v___x_1495_);
                v___x_1501_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_1488_, v___x_1492_);
                v___x_1502_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1502_, 0, v___x_1500_);
                lean_ctor_set(v___x_1502_, 1, v___x_1501_);
                lean_inc(v___y_1494_);
                v___x_1503_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1503_, 0, v___y_1494_);
                lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                v___x_1504_ = 0;
                v___x_1505_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                lean_ctor_set_uint8(
                    v___x_1505_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1504_,
                );
                v___x_1506_ = l_Repr_addAppParen(v___x_1505_, v_prec_1429_);
                return v___x_1506_;
            }
            11 => {
                v___x_1516_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__15;
                v___x_1517_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1512_, v___x_1513_);
                v___x_1518_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1518_, 0, v___x_1516_);
                lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                lean_inc(v___y_1515_);
                v___x_1519_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1519_, 0, v___y_1515_);
                lean_ctor_set(v___x_1519_, 1, v___x_1518_);
                v___x_1520_ = 0;
                v___x_1521_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1521_, 0, v___x_1519_);
                lean_ctor_set_uint8(
                    v___x_1521_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1520_,
                );
                v___x_1522_ = l_Repr_addAppParen(v___x_1521_, v_prec_1429_);
                return v___x_1522_;
            }
            12 => {
                v___x_1531_ = lean_unsigned_to_nat(1024);
                v___x_1548_ = lean_nat_dec_le(v___x_1531_, v_prec_1429_);
                if v___x_1548_ == 0 {
                    v___x_1549_ = lean_obj_once(
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
                    v___x_1550_ = lean_obj_once(
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
                v___x_1534_ = lean_box(1);
                v___x_1535_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__18;
                v___x_1536_ = l_Nat_reprFast(v_k_1526_);
                v___x_1537_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                if v_isShared_1530_ == 0 {
                    lean_ctor_set(v___x_1529_, 1, v___x_1537_);
                    lean_ctor_set(v___x_1529_, 0, v___x_1535_);
                    v___x_1539_ = v___x_1529_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1535_);
                    lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1537_);
                    v___x_1539_ = v_reuseFailAlloc_1547_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1540_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1540_, 0, v___x_1539_);
                lean_ctor_set(v___x_1540_, 1, v___x_1534_);
                v___x_1541_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1527_, v___x_1531_);
                v___x_1542_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1542_, 0, v___x_1540_);
                lean_ctor_set(v___x_1542_, 1, v___x_1541_);
                lean_inc(v___y_1533_);
                v___x_1543_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1543_, 0, v___y_1533_);
                lean_ctor_set(v___x_1543_, 1, v___x_1542_);
                v___x_1544_ = 0;
                v___x_1545_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1545_, 0, v___x_1543_);
                lean_ctor_set_uint8(
                    v___x_1545_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1544_,
                );
                v___x_1546_ = l_Repr_addAppParen(v___x_1545_, v_prec_1429_);
                return v___x_1546_;
            }
            15 => {
                v___x_1557_ = lean_unsigned_to_nat(1024);
                v___x_1584_ = lean_nat_dec_le(v___x_1557_, v_prec_1429_);
                if v___x_1584_ == 0 {
                    v___x_1585_ = lean_obj_once(
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
                    v___x_1586_ = lean_obj_once(
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
                lean_inc(v___y_1559_);
                if v_isShared_1556_ == 0 {
                    lean_ctor_set_tag(v___x_1555_, 5);
                    lean_ctor_set(v___x_1555_, 1, v___y_1562_);
                    lean_ctor_set(v___x_1555_, 0, v___y_1559_);
                    v___x_1564_ = v___x_1555_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1572_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___y_1559_);
                    lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___y_1562_);
                    v___x_1564_ = v_reuseFailAlloc_1572_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                lean_inc(v___y_1561_);
                v___x_1565_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1565_, 0, v___x_1564_);
                lean_ctor_set(v___x_1565_, 1, v___y_1561_);
                v___x_1566_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_1553_, v___x_1557_);
                v___x_1567_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1567_, 0, v___x_1565_);
                lean_ctor_set(v___x_1567_, 1, v___x_1566_);
                lean_inc(v___y_1560_);
                v___x_1568_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1568_, 0, v___y_1560_);
                lean_ctor_set(v___x_1568_, 1, v___x_1567_);
                v___x_1569_ = 0;
                v___x_1570_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1570_, 0, v___x_1568_);
                lean_ctor_set_uint8(
                    v___x_1570_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1569_,
                );
                v___x_1571_ = l_Repr_addAppParen(v___x_1570_, v_prec_1429_);
                return v___x_1571_;
            }
            18 => {
                v___x_1575_ = lean_box(1);
                v___x_1576_ = l_Lean_Grind_Linarith_instReprExpr_repr___closed__21;
                v___x_1577_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                v___x_1578_ = lean_int_dec_lt(v_k_1552_, v___x_1577_);
                if v___x_1578_ == 0 {
                    v___x_1579_ = l_Int_repr(v_k_1552_);
                    lean_dec(v_k_1552_);
                    v___x_1580_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1580_, 0, v___x_1579_);
                    v___y_1559_ = v___x_1576_;
                    v___y_1560_ = v___y_1574_;
                    v___y_1561_ = v___x_1575_;
                    v___y_1562_ = v___x_1580_;
                    state = 16;
                    continue;
                } else {
                    v___x_1581_ = l_Int_repr(v_k_1552_);
                    lean_dec(v_k_1552_);
                    v___x_1582_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1582_, 0, v___x_1581_);
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
    mut v_x_1588_: *mut LeanObject,
    mut v_prec_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1590_: *mut LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_x_1588_, v_prec_1589_);
    lean_dec(v_prec_1589_);
    return v_res_1590_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote___redArg(
    mut v_ctx_1593_: *mut LeanObject,
    mut v_v_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    v___x_1595_ = l_Lean_RArray_getImpl___redArg(v_ctx_1593_, v_v_1594_);
    return v___x_1595_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote___redArg___boxed(
    mut v_ctx_1596_: *mut LeanObject,
    mut v_v_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Grind_Linarith_Var_denote___redArg(v_ctx_1596_, v_v_1597_);
    lean_dec(v_v_1597_);
    lean_dec_ref(v_ctx_1596_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote(
    mut v_00_u03b1_1599_: *mut LeanObject,
    mut v_ctx_1600_: *mut LeanObject,
    mut v_v_1601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_RArray_getImpl___redArg(v_ctx_1600_, v_v_1601_);
    return v___x_1602_;
}
pub unsafe fn l_Lean_Grind_Linarith_Var_denote___boxed(
    mut v_00_u03b1_1603_: *mut LeanObject,
    mut v_ctx_1604_: *mut LeanObject,
    mut v_v_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Lean_Grind_Linarith_Var_denote(v_00_u03b1_1603_, v_ctx_1604_, v_v_1605_);
    lean_dec(v_v_1605_);
    lean_dec_ref(v_ctx_1604_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote___redArg(
    mut v_inst_1607_: *mut LeanObject,
    mut v_ctx_1608_: *mut LeanObject,
    mut v_x_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1611_: *mut LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1607_);
    v_toAddCommMonoid_1611_ = lean_ctor_get(v___x_1610_, 0);
    lean_inc_ref(v_toAddCommMonoid_1611_);
    match lean_obj_tag(v_x_1609_) {
        0 => {
            let mut v_toZero_1612_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_1610_);
            lean_dec_ref(v_inst_1607_);
            v_toZero_1612_ = lean_ctor_get(v_toAddCommMonoid_1611_, 0);
            lean_inc(v_toZero_1612_);
            lean_dec_ref(v_toAddCommMonoid_1611_);
            return v_toZero_1612_;
        }
        1 => {
            let mut v_i_1613_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toAddCommMonoid_1611_);
            lean_dec_ref(v___x_1610_);
            lean_dec_ref(v_inst_1607_);
            v_i_1613_ = lean_ctor_get(v_x_1609_, 0);
            lean_inc(v_i_1613_);
            lean_dec_ref_known(v_x_1609_, 1);
            v___x_1614_ = l_Lean_RArray_getImpl___redArg(v_ctx_1608_, v_i_1613_);
            lean_dec(v_i_1613_);
            return v___x_1614_;
        }
        2 => {
            let mut v_toAdd_1615_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1616_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_1610_);
            v_toAdd_1615_ = lean_ctor_get(v_toAddCommMonoid_1611_, 1);
            lean_inc(v_toAdd_1615_);
            lean_dec_ref(v_toAddCommMonoid_1611_);
            v_a_1616_ = lean_ctor_get(v_x_1609_, 0);
            lean_inc(v_a_1616_);
            v_b_1617_ = lean_ctor_get(v_x_1609_, 1);
            lean_inc(v_b_1617_);
            lean_dec_ref_known(v_x_1609_, 2);
            lean_inc_ref(v_inst_1607_);
            v___x_1618_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1616_);
            v___x_1619_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_b_1617_);
            v___x_1620_ = lean_apply_2(v_toAdd_1615_, v___x_1618_, v___x_1619_);
            return v___x_1620_;
        }
        3 => {
            let mut v_toAddCommGroup_1621_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toSub_1622_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1623_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1624_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
            v_toAddCommGroup_1621_ = lean_ctor_get(v_inst_1607_, 0);
            lean_dec_ref(v_toAddCommMonoid_1611_);
            lean_dec_ref(v___x_1610_);
            v_toSub_1622_ = lean_ctor_get(v_toAddCommGroup_1621_, 2);
            lean_inc(v_toSub_1622_);
            v_a_1623_ = lean_ctor_get(v_x_1609_, 0);
            lean_inc(v_a_1623_);
            v_b_1624_ = lean_ctor_get(v_x_1609_, 1);
            lean_inc(v_b_1624_);
            lean_dec_ref_known(v_x_1609_, 2);
            lean_inc_ref(v_inst_1607_);
            v___x_1625_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1623_);
            v___x_1626_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_b_1624_);
            v___x_1627_ = lean_apply_2(v_toSub_1622_, v___x_1625_, v___x_1626_);
            return v___x_1627_;
        }
        4 => {
            let mut v_toAddCommGroup_1628_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toNeg_1629_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
            v_toAddCommGroup_1628_ = lean_ctor_get(v_inst_1607_, 0);
            lean_dec_ref(v_toAddCommMonoid_1611_);
            lean_dec_ref(v___x_1610_);
            v_toNeg_1629_ = lean_ctor_get(v_toAddCommGroup_1628_, 1);
            lean_inc(v_toNeg_1629_);
            v_a_1630_ = lean_ctor_get(v_x_1609_, 0);
            lean_inc(v_a_1630_);
            lean_dec_ref_known(v_x_1609_, 1);
            v___x_1631_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1630_);
            v___x_1632_ = lean_apply_1(v_toNeg_1629_, v___x_1631_);
            return v___x_1632_;
        }
        5 => {
            let mut v_nsmul_1633_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1634_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1635_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toAddCommMonoid_1611_);
            v_nsmul_1633_ = lean_ctor_get(v___x_1610_, 1);
            lean_inc(v_nsmul_1633_);
            lean_dec_ref(v___x_1610_);
            v_k_1634_ = lean_ctor_get(v_x_1609_, 0);
            lean_inc(v_k_1634_);
            v_a_1635_ = lean_ctor_get(v_x_1609_, 1);
            lean_inc(v_a_1635_);
            lean_dec_ref_known(v_x_1609_, 2);
            v___x_1636_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1635_);
            v___x_1637_ = lean_apply_2(v_nsmul_1633_, v_k_1634_, v___x_1636_);
            return v___x_1637_;
        }
        _ => {
            let mut v_zsmul_1638_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1639_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1640_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toAddCommMonoid_1611_);
            lean_dec_ref(v___x_1610_);
            v_zsmul_1638_ = lean_ctor_get(v_inst_1607_, 2);
            lean_inc(v_zsmul_1638_);
            v_k_1639_ = lean_ctor_get(v_x_1609_, 0);
            lean_inc(v_k_1639_);
            v_a_1640_ = lean_ctor_get(v_x_1609_, 1);
            lean_inc(v_a_1640_);
            lean_dec_ref_known(v_x_1609_, 2);
            v___x_1641_ =
                l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1607_, v_ctx_1608_, v_a_1640_);
            v___x_1642_ = lean_apply_2(v_zsmul_1638_, v_k_1639_, v___x_1641_);
            return v___x_1642_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(
    mut v_inst_1643_: *mut LeanObject,
    mut v_ctx_1644_: *mut LeanObject,
    mut v_x_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1646_: *mut LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1643_, v_ctx_1644_, v_x_1645_);
    lean_dec_ref(v_ctx_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote(
    mut v_00_u03b1_1647_: *mut LeanObject,
    mut v_inst_1648_: *mut LeanObject,
    mut v_ctx_1649_: *mut LeanObject,
    mut v_x_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_1648_, v_ctx_1649_, v_x_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denote___boxed(
    mut v_00_u03b1_1652_: *mut LeanObject,
    mut v_inst_1653_: *mut LeanObject,
    mut v_ctx_1654_: *mut LeanObject,
    mut v_x_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1656_: *mut LeanObject = core::ptr::null_mut();
    v_res_1656_ =
        l_Lean_Grind_Linarith_Expr_denote(v_00_u03b1_1652_, v_inst_1653_, v_ctx_1654_, v_x_1655_);
    lean_dec_ref(v_ctx_1654_);
    return v_res_1656_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorIdx(
    mut v_x_1657_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1657_) == 0 {
        let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
        v___x_1658_ = lean_unsigned_to_nat(0);
        return v___x_1658_;
    } else {
        let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
        v___x_1659_ = lean_unsigned_to_nat(1);
        return v___x_1659_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorIdx___boxed(
    mut v_x_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1661_: *mut LeanObject = core::ptr::null_mut();
    v_res_1661_ = l_Lean_Grind_Linarith_Poly_ctorIdx(v_x_1660_);
    lean_dec(v_x_1660_);
    return v_res_1661_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorElim___redArg(
    mut v_t_1662_: *mut LeanObject,
    mut v_k_1663_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1662_) == 0 {
        return v_k_1663_;
    } else {
        let mut v_k_1664_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        v_k_1664_ = lean_ctor_get(v_t_1662_, 0);
        lean_inc(v_k_1664_);
        v_v_1665_ = lean_ctor_get(v_t_1662_, 1);
        lean_inc(v_v_1665_);
        v_p_1666_ = lean_ctor_get(v_t_1662_, 2);
        lean_inc(v_p_1666_);
        lean_dec_ref_known(v_t_1662_, 3);
        v___x_1667_ = lean_apply_3(v_k_1663_, v_k_1664_, v_v_1665_, v_p_1666_);
        return v___x_1667_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorElim(
    mut v_motive_1668_: *mut LeanObject,
    mut v_ctorIdx_1669_: *mut LeanObject,
    mut v_t_1670_: *mut LeanObject,
    mut v_h_1671_: *mut LeanObject,
    mut v_k_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1670_, v_k_1672_);
    return v___x_1673_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_ctorElim___boxed(
    mut v_motive_1674_: *mut LeanObject,
    mut v_ctorIdx_1675_: *mut LeanObject,
    mut v_t_1676_: *mut LeanObject,
    mut v_h_1677_: *mut LeanObject,
    mut v_k_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1679_: *mut LeanObject = core::ptr::null_mut();
    v_res_1679_ = l_Lean_Grind_Linarith_Poly_ctorElim(
        v_motive_1674_,
        v_ctorIdx_1675_,
        v_t_1676_,
        v_h_1677_,
        v_k_1678_,
    );
    lean_dec(v_ctorIdx_1675_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_nil_elim___redArg(
    mut v_t_1680_: *mut LeanObject,
    mut v_nil_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1680_, v_nil_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_nil_elim(
    mut v_motive_1683_: *mut LeanObject,
    mut v_t_1684_: *mut LeanObject,
    mut v_h_1685_: *mut LeanObject,
    mut v_nil_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1684_, v_nil_1686_);
    return v___x_1687_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_add_elim___redArg(
    mut v_t_1688_: *mut LeanObject,
    mut v_add_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    v___x_1690_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1688_, v_add_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_add_elim(
    mut v_motive_1691_: *mut LeanObject,
    mut v_t_1692_: *mut LeanObject,
    mut v_h_1693_: *mut LeanObject,
    mut v_add_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_1692_, v_add_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Lean_Grind_Linarith_instBEqPoly_beq(
    mut v_x_1696_: *mut LeanObject,
    mut v_x_1697_: *mut LeanObject,
) -> u8 {
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: u8 = 0;
    let mut v_k_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1696_) == 0 {
                    if lean_obj_tag(v_x_1697_) == 0 {
                        v___x_1698_ = 1;
                        return v___x_1698_;
                    } else {
                        v___x_1699_ = 0;
                        return v___x_1699_;
                    }
                } else {
                    if lean_obj_tag(v_x_1697_) == 1 {
                        v_k_1700_ = lean_ctor_get(v_x_1696_, 0);
                        v_v_1701_ = lean_ctor_get(v_x_1696_, 1);
                        v_p_1702_ = lean_ctor_get(v_x_1696_, 2);
                        v_k_1703_ = lean_ctor_get(v_x_1697_, 0);
                        v_v_1704_ = lean_ctor_get(v_x_1697_, 1);
                        v_p_1705_ = lean_ctor_get(v_x_1697_, 2);
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
    mut v_x_1710_: *mut LeanObject,
    mut v_x_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1712_: u8 = 0;
    let mut v_r_1713_: *mut LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_1710_, v_x_1711_);
    lean_dec(v_x_1711_);
    lean_dec(v_x_1710_);
    v_r_1713_ = lean_box((v_res_1712_) as usize);
    return v_r_1713_;
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(
    mut v_x_1716_: *mut LeanObject,
    mut v_x_1717_: *mut LeanObject,
    mut v_h__1_1718_: *mut LeanObject,
    mut v_h__2_1719_: *mut LeanObject,
    mut v_h__3_1720_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1716_) == 0 {
        lean_dec(v_h__2_1719_);
        if lean_obj_tag(v_x_1717_) == 0 {
            let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1720_);
            v___x_1721_ = lean_box(0);
            v___x_1722_ = lean_apply_1(v_h__1_1718_, v___x_1721_);
            return v___x_1722_;
        } else {
            let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1718_);
            v___x_1723_ =
                lean_apply_4(v_h__3_1720_, v_x_1716_, v_x_1717_, lean_box(0), lean_box(0));
            return v___x_1723_;
        }
    } else {
        lean_dec(v_h__1_1718_);
        if lean_obj_tag(v_x_1717_) == 1 {
            let mut v_k_1724_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_1725_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1726_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1727_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_1728_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1729_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1720_);
            v_k_1724_ = lean_ctor_get(v_x_1716_, 0);
            lean_inc(v_k_1724_);
            v_v_1725_ = lean_ctor_get(v_x_1716_, 1);
            lean_inc(v_v_1725_);
            v_p_1726_ = lean_ctor_get(v_x_1716_, 2);
            lean_inc(v_p_1726_);
            lean_dec_ref_known(v_x_1716_, 3);
            v_k_1727_ = lean_ctor_get(v_x_1717_, 0);
            lean_inc(v_k_1727_);
            v_v_1728_ = lean_ctor_get(v_x_1717_, 1);
            lean_inc(v_v_1728_);
            v_p_1729_ = lean_ctor_get(v_x_1717_, 2);
            lean_inc(v_p_1729_);
            lean_dec_ref_known(v_x_1717_, 3);
            v___x_1730_ = lean_apply_6(
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
            let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1719_);
            v___x_1731_ =
                lean_apply_4(v_h__3_1720_, v_x_1716_, v_x_1717_, lean_box(0), lean_box(0));
            return v___x_1731_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(
    mut v_motive_1732_: *mut LeanObject,
    mut v_x_1733_: *mut LeanObject,
    mut v_x_1734_: *mut LeanObject,
    mut v_h__1_1735_: *mut LeanObject,
    mut v_h__2_1736_: *mut LeanObject,
    mut v_h__3_1737_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1733_) == 0 {
        lean_dec(v_h__2_1736_);
        if lean_obj_tag(v_x_1734_) == 0 {
            let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1737_);
            v___x_1738_ = lean_box(0);
            v___x_1739_ = lean_apply_1(v_h__1_1735_, v___x_1738_);
            return v___x_1739_;
        } else {
            let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1735_);
            v___x_1740_ =
                lean_apply_4(v_h__3_1737_, v_x_1733_, v_x_1734_, lean_box(0), lean_box(0));
            return v___x_1740_;
        }
    } else {
        lean_dec(v_h__1_1735_);
        if lean_obj_tag(v_x_1734_) == 1 {
            let mut v_k_1741_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_1742_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1743_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1744_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_1745_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1746_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1737_);
            v_k_1741_ = lean_ctor_get(v_x_1733_, 0);
            lean_inc(v_k_1741_);
            v_v_1742_ = lean_ctor_get(v_x_1733_, 1);
            lean_inc(v_v_1742_);
            v_p_1743_ = lean_ctor_get(v_x_1733_, 2);
            lean_inc(v_p_1743_);
            lean_dec_ref_known(v_x_1733_, 3);
            v_k_1744_ = lean_ctor_get(v_x_1734_, 0);
            lean_inc(v_k_1744_);
            v_v_1745_ = lean_ctor_get(v_x_1734_, 1);
            lean_inc(v_v_1745_);
            v_p_1746_ = lean_ctor_get(v_x_1734_, 2);
            lean_inc(v_p_1746_);
            lean_dec_ref_known(v_x_1734_, 3);
            v___x_1747_ = lean_apply_6(
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
            let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1736_);
            v___x_1748_ =
                lean_apply_4(v_h__3_1737_, v_x_1733_, v_x_1734_, lean_box(0), lean_box(0));
            return v___x_1748_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_instReprPoly_repr(
    mut v_x_1758_: *mut LeanObject,
    mut v_prec_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1758_) == 0 {
                    v___x_1767_ = lean_unsigned_to_nat(1024);
                    v___x_1768_ = lean_nat_dec_le(v___x_1767_, v_prec_1759_);
                    if v___x_1768_ == 0 {
                        v___x_1769_ = lean_obj_once(
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
                        v___x_1770_ = lean_obj_once(
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
                    v_k_1771_ = lean_ctor_get(v_x_1758_, 0);
                    lean_inc(v_k_1771_);
                    v_v_1772_ = lean_ctor_get(v_x_1758_, 1);
                    lean_inc(v_v_1772_);
                    v_p_1773_ = lean_ctor_get(v_x_1758_, 2);
                    lean_inc(v_p_1773_);
                    lean_dec_ref_known(v_x_1758_, 3);
                    v___x_1774_ = lean_unsigned_to_nat(1024);
                    v___x_1803_ = lean_nat_dec_le(v___x_1774_, v_prec_1759_);
                    if v___x_1803_ == 0 {
                        v___x_1804_ = lean_obj_once(
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
                        v___x_1805_ = lean_obj_once(
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
                lean_inc(v___y_1761_);
                v___x_1763_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1763_, 0, v___y_1761_);
                lean_ctor_set(v___x_1763_, 1, v___x_1762_);
                v___x_1764_ = 0;
                v___x_1765_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1765_, 0, v___x_1763_);
                lean_ctor_set_uint8(
                    v___x_1765_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1764_,
                );
                v___x_1766_ = l_Repr_addAppParen(v___x_1765_, v_prec_1759_);
                return v___x_1766_;
            }
            2 => {
                lean_inc(v___y_1778_);
                v___x_1780_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1780_, 0, v___y_1778_);
                lean_ctor_set(v___x_1780_, 1, v___y_1779_);
                lean_inc_n(v___y_1776_, 2);
                v___x_1781_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1781_, 0, v___x_1780_);
                lean_ctor_set(v___x_1781_, 1, v___y_1776_);
                v___x_1782_ = l_Nat_reprFast(v_v_1772_);
                v___x_1783_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1783_, 0, v___x_1782_);
                v___x_1784_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1784_, 0, v___x_1781_);
                lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                v___x_1785_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1785_, 0, v___x_1784_);
                lean_ctor_set(v___x_1785_, 1, v___y_1776_);
                v___x_1786_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_p_1773_, v___x_1774_);
                v___x_1787_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1787_, 0, v___x_1785_);
                lean_ctor_set(v___x_1787_, 1, v___x_1786_);
                lean_inc(v___y_1777_);
                v___x_1788_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1788_, 0, v___y_1777_);
                lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = 0;
                v___x_1790_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1790_, 0, v___x_1788_);
                lean_ctor_set_uint8(
                    v___x_1790_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1789_,
                );
                v___x_1791_ = l_Repr_addAppParen(v___x_1790_, v_prec_1759_);
                return v___x_1791_;
            }
            3 => {
                v___x_1794_ = lean_box(1);
                v___x_1795_ = l_Lean_Grind_Linarith_instReprPoly_repr___closed__4;
                v___x_1796_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                v___x_1797_ = lean_int_dec_lt(v_k_1771_, v___x_1796_);
                if v___x_1797_ == 0 {
                    v___x_1798_ = l_Int_repr(v_k_1771_);
                    lean_dec(v_k_1771_);
                    v___x_1799_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1799_, 0, v___x_1798_);
                    v___y_1776_ = v___x_1794_;
                    v___y_1777_ = v___y_1793_;
                    v___y_1778_ = v___x_1795_;
                    v___y_1779_ = v___x_1799_;
                    state = 2;
                    continue;
                } else {
                    v___x_1800_ = l_Int_repr(v_k_1771_);
                    lean_dec(v_k_1771_);
                    v___x_1801_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1801_, 0, v___x_1800_);
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
    mut v_x_1806_: *mut LeanObject,
    mut v_prec_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1808_: *mut LeanObject = core::ptr::null_mut();
    v_res_1808_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_x_1806_, v_prec_1807_);
    lean_dec(v_prec_1807_);
    return v_res_1808_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote___redArg(
    mut v_inst_1811_: *mut LeanObject,
    mut v_ctx_1812_: *mut LeanObject,
    mut v_p_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1815_: *mut LeanObject = core::ptr::null_mut();
    v___x_1814_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1811_);
    v_toAddCommMonoid_1815_ = lean_ctor_get(v___x_1814_, 0);
    lean_inc_ref(v_toAddCommMonoid_1815_);
    lean_dec_ref(v___x_1814_);
    if lean_obj_tag(v_p_1813_) == 0 {
        let mut v_toZero_1816_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1811_);
        v_toZero_1816_ = lean_ctor_get(v_toAddCommMonoid_1815_, 0);
        lean_inc(v_toZero_1816_);
        lean_dec_ref(v_toAddCommMonoid_1815_);
        return v_toZero_1816_;
    } else {
        let mut v_toAdd_1817_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zsmul_1818_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1819_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1820_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
        v_toAdd_1817_ = lean_ctor_get(v_toAddCommMonoid_1815_, 1);
        lean_inc(v_toAdd_1817_);
        lean_dec_ref(v_toAddCommMonoid_1815_);
        v_zsmul_1818_ = lean_ctor_get(v_inst_1811_, 2);
        v_k_1819_ = lean_ctor_get(v_p_1813_, 0);
        lean_inc(v_k_1819_);
        v_v_1820_ = lean_ctor_get(v_p_1813_, 1);
        lean_inc(v_v_1820_);
        v_p_1821_ = lean_ctor_get(v_p_1813_, 2);
        lean_inc(v_p_1821_);
        lean_dec_ref_known(v_p_1813_, 3);
        v___x_1822_ = l_Lean_RArray_getImpl___redArg(v_ctx_1812_, v_v_1820_);
        lean_dec(v_v_1820_);
        lean_inc(v_zsmul_1818_);
        v___x_1823_ = lean_apply_2(v_zsmul_1818_, v_k_1819_, v___x_1822_);
        v___x_1824_ =
            l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_1811_, v_ctx_1812_, v_p_1821_);
        v___x_1825_ = lean_apply_2(v_toAdd_1817_, v___x_1823_, v___x_1824_);
        return v___x_1825_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(
    mut v_inst_1826_: *mut LeanObject,
    mut v_ctx_1827_: *mut LeanObject,
    mut v_p_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1829_: *mut LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_1826_, v_ctx_1827_, v_p_1828_);
    lean_dec_ref(v_ctx_1827_);
    return v_res_1829_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote(
    mut v_00_u03b1_1830_: *mut LeanObject,
    mut v_inst_1831_: *mut LeanObject,
    mut v_ctx_1832_: *mut LeanObject,
    mut v_p_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_1831_, v_ctx_1832_, v_p_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote___boxed(
    mut v_00_u03b1_1835_: *mut LeanObject,
    mut v_inst_1836_: *mut LeanObject,
    mut v_ctx_1837_: *mut LeanObject,
    mut v_p_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ =
        l_Lean_Grind_Linarith_Poly_denote(v_00_u03b1_1835_, v_inst_1836_, v_ctx_1837_, v_p_1838_);
    lean_dec_ref(v_ctx_1837_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
    mut v_inst_1840_: *mut LeanObject,
    mut v_ctx_1841_: *mut LeanObject,
    mut v_r_1842_: *mut LeanObject,
    mut v_p_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAdd_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmul_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1844_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1840_);
                v_toAddCommMonoid_1845_ = lean_ctor_get(v___x_1844_, 0);
                lean_inc_ref(v_toAddCommMonoid_1845_);
                lean_dec_ref(v___x_1844_);
                if lean_obj_tag(v_p_1843_) == 0 {
                    lean_dec_ref(v_toAddCommMonoid_1845_);
                    lean_dec_ref(v_inst_1840_);
                    return v_r_1842_;
                } else {
                    v_toAdd_1846_ = lean_ctor_get(v_toAddCommMonoid_1845_, 1);
                    lean_inc(v_toAdd_1846_);
                    lean_dec_ref(v_toAddCommMonoid_1845_);
                    v_zsmul_1847_ = lean_ctor_get(v_inst_1840_, 2);
                    v_k_1848_ = lean_ctor_get(v_p_1843_, 0);
                    lean_inc(v_k_1848_);
                    v_v_1849_ = lean_ctor_get(v_p_1843_, 1);
                    lean_inc(v_v_1849_);
                    v_p_1850_ = lean_ctor_get(v_p_1843_, 2);
                    lean_inc(v_p_1850_);
                    lean_dec_ref_known(v_p_1843_, 3);
                    v___x_1851_ = lean_obj_once(
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
                        lean_dec(v_v_1849_);
                        lean_inc(v_zsmul_1847_);
                        v___x_1854_ = lean_apply_2(v_zsmul_1847_, v_k_1848_, v___x_1853_);
                        v___x_1855_ = lean_apply_2(v_toAdd_1846_, v_r_1842_, v___x_1854_);
                        v_r_1842_ = v___x_1855_;
                        v_p_1843_ = v_p_1850_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_k_1848_);
                        v___x_1857_ = l_Lean_RArray_getImpl___redArg(v_ctx_1841_, v_v_1849_);
                        lean_dec(v_v_1849_);
                        v___x_1858_ = lean_apply_2(v_toAdd_1846_, v_r_1842_, v___x_1857_);
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
    mut v_inst_1860_: *mut LeanObject,
    mut v_ctx_1861_: *mut LeanObject,
    mut v_r_1862_: *mut LeanObject,
    mut v_p_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1864_: *mut LeanObject = core::ptr::null_mut();
    v_res_1864_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
        v_inst_1860_,
        v_ctx_1861_,
        v_r_1862_,
        v_p_1863_,
    );
    lean_dec_ref(v_ctx_1861_);
    return v_res_1864_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go(
    mut v_00_u03b1_1865_: *mut LeanObject,
    mut v_inst_1866_: *mut LeanObject,
    mut v_ctx_1867_: *mut LeanObject,
    mut v_r_1868_: *mut LeanObject,
    mut v_p_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
        v_inst_1866_,
        v_ctx_1867_,
        v_r_1868_,
        v_p_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(
    mut v_00_u03b1_1871_: *mut LeanObject,
    mut v_inst_1872_: *mut LeanObject,
    mut v_ctx_1873_: *mut LeanObject,
    mut v_r_1874_: *mut LeanObject,
    mut v_p_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1876_: *mut LeanObject = core::ptr::null_mut();
    v_res_1876_ = l_Lean_Grind_Linarith_Poly_denote_x27_go(
        v_00_u03b1_1871_,
        v_inst_1872_,
        v_ctx_1873_,
        v_r_1874_,
        v_p_1875_,
    );
    lean_dec_ref(v_ctx_1873_);
    return v_res_1876_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27___redArg(
    mut v_inst_1877_: *mut LeanObject,
    mut v_ctx_1878_: *mut LeanObject,
    mut v_p_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1881_: *mut LeanObject = core::ptr::null_mut();
    v___x_1880_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1877_);
    v_toAddCommMonoid_1881_ = lean_ctor_get(v___x_1880_, 0);
    lean_inc_ref(v_toAddCommMonoid_1881_);
    lean_dec_ref(v___x_1880_);
    if lean_obj_tag(v_p_1879_) == 0 {
        let mut v_toZero_1882_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1877_);
        v_toZero_1882_ = lean_ctor_get(v_toAddCommMonoid_1881_, 0);
        lean_inc(v_toZero_1882_);
        lean_dec_ref(v_toAddCommMonoid_1881_);
        return v_toZero_1882_;
    } else {
        let mut v_zsmul_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1884_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: u8 = 0;
        lean_dec_ref(v_toAddCommMonoid_1881_);
        v_zsmul_1883_ = lean_ctor_get(v_inst_1877_, 2);
        v_k_1884_ = lean_ctor_get(v_p_1879_, 0);
        lean_inc(v_k_1884_);
        v_v_1885_ = lean_ctor_get(v_p_1879_, 1);
        lean_inc(v_v_1885_);
        v_p_1886_ = lean_ctor_get(v_p_1879_, 2);
        lean_inc(v_p_1886_);
        lean_dec_ref_known(v_p_1879_, 3);
        v___x_1887_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1888_ = lean_int_dec_eq(v_k_1884_, v___x_1887_);
        if v___x_1888_ == 0 {
            let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
            v___x_1889_ = l_Lean_RArray_getImpl___redArg(v_ctx_1878_, v_v_1885_);
            lean_dec(v_v_1885_);
            lean_inc(v_zsmul_1883_);
            v___x_1890_ = lean_apply_2(v_zsmul_1883_, v_k_1884_, v___x_1889_);
            v___x_1891_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
                v_inst_1877_,
                v_ctx_1878_,
                v___x_1890_,
                v_p_1886_,
            );
            return v___x_1891_;
        } else {
            let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_1884_);
            v___x_1892_ = l_Lean_RArray_getImpl___redArg(v_ctx_1878_, v_v_1885_);
            lean_dec(v_v_1885_);
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
    mut v_inst_1894_: *mut LeanObject,
    mut v_ctx_1895_: *mut LeanObject,
    mut v_p_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ =
        l_Lean_Grind_Linarith_Poly_denote_x27___redArg(v_inst_1894_, v_ctx_1895_, v_p_1896_);
    lean_dec_ref(v_ctx_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denote_x27(
    mut v_00_u03b1_1898_: *mut LeanObject,
    mut v_inst_1899_: *mut LeanObject,
    mut v_ctx_1900_: *mut LeanObject,
    mut v_p_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1903_: *mut LeanObject = core::ptr::null_mut();
    v___x_1902_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_1899_);
    v_toAddCommMonoid_1903_ = lean_ctor_get(v___x_1902_, 0);
    lean_inc_ref(v_toAddCommMonoid_1903_);
    lean_dec_ref(v___x_1902_);
    if lean_obj_tag(v_p_1901_) == 0 {
        let mut v_toZero_1904_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1899_);
        v_toZero_1904_ = lean_ctor_get(v_toAddCommMonoid_1903_, 0);
        lean_inc(v_toZero_1904_);
        lean_dec_ref(v_toAddCommMonoid_1903_);
        return v_toZero_1904_;
    } else {
        let mut v_zsmul_1905_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1906_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1907_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: u8 = 0;
        lean_dec_ref(v_toAddCommMonoid_1903_);
        v_zsmul_1905_ = lean_ctor_get(v_inst_1899_, 2);
        v_k_1906_ = lean_ctor_get(v_p_1901_, 0);
        lean_inc(v_k_1906_);
        v_v_1907_ = lean_ctor_get(v_p_1901_, 1);
        lean_inc(v_v_1907_);
        v_p_1908_ = lean_ctor_get(v_p_1901_, 2);
        lean_inc(v_p_1908_);
        lean_dec_ref_known(v_p_1901_, 3);
        v___x_1909_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1910_ = lean_int_dec_eq(v_k_1906_, v___x_1909_);
        if v___x_1910_ == 0 {
            let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
            v___x_1911_ = l_Lean_RArray_getImpl___redArg(v_ctx_1900_, v_v_1907_);
            lean_dec(v_v_1907_);
            lean_inc(v_zsmul_1905_);
            v___x_1912_ = lean_apply_2(v_zsmul_1905_, v_k_1906_, v___x_1911_);
            v___x_1913_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(
                v_inst_1899_,
                v_ctx_1900_,
                v___x_1912_,
                v_p_1908_,
            );
            return v___x_1913_;
        } else {
            let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_1906_);
            v___x_1914_ = l_Lean_RArray_getImpl___redArg(v_ctx_1900_, v_v_1907_);
            lean_dec(v_v_1907_);
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
    mut v_00_u03b1_1916_: *mut LeanObject,
    mut v_inst_1917_: *mut LeanObject,
    mut v_ctx_1918_: *mut LeanObject,
    mut v_p_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Grind_Linarith_Poly_denote_x27(
        v_00_u03b1_1916_,
        v_inst_1917_,
        v_ctx_1918_,
        v_p_1919_,
    );
    lean_dec_ref(v_ctx_1918_);
    return v_res_1920_;
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(
    mut v_p_1921_: *mut LeanObject,
    mut v_h__1_1922_: *mut LeanObject,
    mut v_h__2_1923_: *mut LeanObject,
    mut v_h__3_1924_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_1921_) == 0 {
        let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1924_);
        lean_dec(v_h__2_1923_);
        v___x_1925_ = lean_box(0);
        v___x_1926_ = lean_apply_1(v_h__1_1922_, v___x_1925_);
        return v___x_1926_;
    } else {
        let mut v_k_1927_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1928_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: u8 = 0;
        lean_dec(v_h__1_1922_);
        v_k_1927_ = lean_ctor_get(v_p_1921_, 0);
        lean_inc(v_k_1927_);
        v_v_1928_ = lean_ctor_get(v_p_1921_, 1);
        lean_inc(v_v_1928_);
        v_p_1929_ = lean_ctor_get(v_p_1921_, 2);
        lean_inc(v_p_1929_);
        lean_dec_ref_known(v_p_1921_, 3);
        v___x_1930_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1931_ = lean_int_dec_eq(v_k_1927_, v___x_1930_);
        if v___x_1931_ == 0 {
            let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1923_);
            v___x_1932_ = lean_apply_4(v_h__3_1924_, v_k_1927_, v_v_1928_, v_p_1929_, lean_box(0));
            return v___x_1932_;
        } else {
            let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_1927_);
            lean_dec(v_h__3_1924_);
            v___x_1933_ = lean_apply_2(v_h__2_1923_, v_v_1928_, v_p_1929_);
            return v___x_1933_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(
    mut v_motive_1934_: *mut LeanObject,
    mut v_p_1935_: *mut LeanObject,
    mut v_h__1_1936_: *mut LeanObject,
    mut v_h__2_1937_: *mut LeanObject,
    mut v_h__3_1938_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_1935_) == 0 {
        let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1938_);
        lean_dec(v_h__2_1937_);
        v___x_1939_ = lean_box(0);
        v___x_1940_ = lean_apply_1(v_h__1_1936_, v___x_1939_);
        return v___x_1940_;
    } else {
        let mut v_k_1941_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1942_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: u8 = 0;
        lean_dec(v_h__1_1936_);
        v_k_1941_ = lean_ctor_get(v_p_1935_, 0);
        lean_inc(v_k_1941_);
        v_v_1942_ = lean_ctor_get(v_p_1935_, 1);
        lean_inc(v_v_1942_);
        v_p_1943_ = lean_ctor_get(v_p_1935_, 2);
        lean_inc(v_p_1943_);
        lean_dec_ref_known(v_p_1935_, 3);
        v___x_1944_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        v___x_1945_ = lean_int_dec_eq(v_k_1941_, v___x_1944_);
        if v___x_1945_ == 0 {
            let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1937_);
            v___x_1946_ = lean_apply_4(v_h__3_1938_, v_k_1941_, v_v_1942_, v_p_1943_, lean_box(0));
            return v___x_1946_;
        } else {
            let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_1941_);
            lean_dec(v_h__3_1938_);
            v___x_1947_ = lean_apply_2(v_h__2_1937_, v_v_1942_, v_p_1943_);
            return v___x_1947_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_coeff(
    mut v_p_1948_: *mut LeanObject,
    mut v_x_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_1948_) == 0 {
                    v___x_1950_ = lean_obj_once(
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
                    v_k_1951_ = lean_ctor_get(v_p_1948_, 0);
                    v_v_1952_ = lean_ctor_get(v_p_1948_, 1);
                    v_p_1953_ = lean_ctor_get(v_p_1948_, 2);
                    v___x_1954_ = lean_nat_dec_eq(v_x_1949_, v_v_1952_);
                    if v___x_1954_ == 0 {
                        v_p_1948_ = v_p_1953_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_k_1951_);
                        return v_k_1951_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_coeff___boxed(
    mut v_p_1956_: *mut LeanObject,
    mut v_x_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1958_: *mut LeanObject = core::ptr::null_mut();
    v_res_1958_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_1956_, v_x_1957_);
    lean_dec(v_x_1957_);
    lean_dec(v_p_1956_);
    return v_res_1958_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_insert(
    mut v_k_1959_: *mut LeanObject,
    mut v_v_1960_: *mut LeanObject,
    mut v_p_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_unused_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_1961_) == 0 {
                    v___x_1962_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1962_, 0, v_k_1959_);
                    lean_ctor_set(v___x_1962_, 1, v_v_1960_);
                    lean_ctor_set(v___x_1962_, 2, v_p_1961_);
                    return v___x_1962_;
                } else {
                    v_k_1963_ = lean_ctor_get(v_p_1961_, 0);
                    v_v_1964_ = lean_ctor_get(v_p_1961_, 1);
                    v_p_1965_ = lean_ctor_get(v_p_1961_, 2);
                    v___x_1966_ = l_Nat_blt(v_v_1964_, v_v_1960_);
                    if v___x_1966_ == 0 {
                        lean_inc(v_p_1965_);
                        lean_inc(v_v_1964_);
                        lean_inc(v_k_1963_);
                        v_isSharedCheck_1981_ = (!lean_is_exclusive(v_p_1961_)) as u8;
                        if v_isSharedCheck_1981_ == 0 {
                            v_unused_1982_ = lean_ctor_get(v_p_1961_, 2);
                            lean_dec(v_unused_1982_);
                            v_unused_1983_ = lean_ctor_get(v_p_1961_, 1);
                            lean_dec(v_unused_1983_);
                            v_unused_1984_ = lean_ctor_get(v_p_1961_, 0);
                            lean_dec(v_unused_1984_);
                            v___x_1968_ = v_p_1961_;
                            v_isShared_1969_ = v_isSharedCheck_1981_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_p_1961_);
                            v___x_1968_ = lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_1981_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1985_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_1985_, 0, v_k_1959_);
                        lean_ctor_set(v___x_1985_, 1, v_v_1960_);
                        lean_ctor_set(v___x_1985_, 2, v_p_1961_);
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
                        lean_ctor_set(v___x_1968_, 2, v___x_1971_);
                        v___x_1973_ = v___x_1968_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_k_1963_);
                        lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_v_1964_);
                        lean_ctor_set(v_reuseFailAlloc_1974_, 2, v___x_1971_);
                        v___x_1973_ = v_reuseFailAlloc_1974_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_v_1960_);
                    v___x_1975_ = lean_int_add(v_k_1959_, v_k_1963_);
                    lean_dec(v_k_1963_);
                    lean_dec(v_k_1959_);
                    v___x_1976_ = lean_obj_once(
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
                            lean_ctor_set(v___x_1968_, 0, v___x_1975_);
                            v___x_1979_ = v___x_1968_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1975_);
                            lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_v_1964_);
                            lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_p_1965_);
                            v___x_1979_ = v_reuseFailAlloc_1980_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1975_);
                        lean_del_object(v___x_1968_);
                        lean_dec(v_v_1964_);
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
pub unsafe fn l_Lean_Grind_Linarith_Poly_norm(mut v_p_1986_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_p_1986_) == 0 {
        return v_p_1986_;
    } else {
        let mut v_k_1987_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1988_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
        v_k_1987_ = lean_ctor_get(v_p_1986_, 0);
        lean_inc(v_k_1987_);
        v_v_1988_ = lean_ctor_get(v_p_1986_, 1);
        lean_inc(v_v_1988_);
        v_p_1989_ = lean_ctor_get(v_p_1986_, 2);
        lean_inc(v_p_1989_);
        lean_dec_ref_known(v_p_1986_, 3);
        v___x_1990_ = l_Lean_Grind_Linarith_Poly_norm(v_p_1989_);
        v___x_1991_ = l_Lean_Grind_Linarith_Poly_insert(v_k_1987_, v_v_1988_, v___x_1990_);
        return v___x_1991_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_append(
    mut v_p_u2081_1992_: *mut LeanObject,
    mut v_p_u2082_1993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_1992_) == 0 {
                    lean_inc(v_p_u2082_1993_);
                    return v_p_u2082_1993_;
                } else {
                    v_k_1994_ = lean_ctor_get(v_p_u2081_1992_, 0);
                    v_v_1995_ = lean_ctor_get(v_p_u2081_1992_, 1);
                    v_p_1996_ = lean_ctor_get(v_p_u2081_1992_, 2);
                    v_isSharedCheck_2004_ = (!lean_is_exclusive(v_p_u2081_1992_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v___x_1998_ = v_p_u2081_1992_;
                        v_isShared_1999_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_1996_);
                        lean_inc(v_v_1995_);
                        lean_inc(v_k_1994_);
                        lean_dec(v_p_u2081_1992_);
                        v___x_1998_ = lean_box(0);
                        v_isShared_1999_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2000_ = l_Lean_Grind_Linarith_Poly_append(v_p_1996_, v_p_u2082_1993_);
                if v_isShared_1999_ == 0 {
                    lean_ctor_set(v___x_1998_, 2, v___x_2000_);
                    v___x_2002_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_k_1994_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_v_1995_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 2, v___x_2000_);
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
    mut v_p_u2081_2005_: *mut LeanObject,
    mut v_p_u2082_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2007_: *mut LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Grind_Linarith_Poly_append(v_p_u2081_2005_, v_p_u2082_2006_);
    lean_dec(v_p_u2082_2006_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_combine(
    mut v_p_u2081_2008_: *mut LeanObject,
    mut v_p_u2082_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_unused_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2031_: u8 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_unused_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v_a_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2051_: u8 = 0;
    let mut v_unused_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_2008_) == 0 {
                    return v_p_u2082_2009_;
                } else {
                    if lean_obj_tag(v_p_u2082_2009_) == 0 {
                        return v_p_u2081_2008_;
                    } else {
                        v_k_2010_ = lean_ctor_get(v_p_u2081_2008_, 0);
                        v_v_2011_ = lean_ctor_get(v_p_u2081_2008_, 1);
                        v_p_2012_ = lean_ctor_get(v_p_u2081_2008_, 2);
                        v_k_2013_ = lean_ctor_get(v_p_u2082_2009_, 0);
                        v_v_2014_ = lean_ctor_get(v_p_u2082_2009_, 1);
                        v_p_2015_ = lean_ctor_get(v_p_u2082_2009_, 2);
                        v___x_2016_ = lean_nat_dec_eq(v_v_2011_, v_v_2014_);
                        if v___x_2016_ == 0 {
                            v___x_2017_ = l_Nat_blt(v_v_2014_, v_v_2011_);
                            if v___x_2017_ == 0 {
                                lean_inc(v_p_2015_);
                                lean_inc(v_v_2014_);
                                lean_inc(v_k_2013_);
                                v_isSharedCheck_2025_ = (!lean_is_exclusive(v_p_u2082_2009_)) as u8;
                                if v_isSharedCheck_2025_ == 0 {
                                    v_unused_2026_ = lean_ctor_get(v_p_u2082_2009_, 2);
                                    lean_dec(v_unused_2026_);
                                    v_unused_2027_ = lean_ctor_get(v_p_u2082_2009_, 1);
                                    lean_dec(v_unused_2027_);
                                    v_unused_2028_ = lean_ctor_get(v_p_u2082_2009_, 0);
                                    lean_dec(v_unused_2028_);
                                    v___x_2019_ = v_p_u2082_2009_;
                                    v_isShared_2020_ = v_isSharedCheck_2025_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2082_2009_);
                                    v___x_2019_ = lean_box(0);
                                    v_isShared_2020_ = v_isSharedCheck_2025_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_inc(v_p_2012_);
                                lean_inc(v_v_2011_);
                                lean_inc(v_k_2010_);
                                v_isSharedCheck_2036_ = (!lean_is_exclusive(v_p_u2081_2008_)) as u8;
                                if v_isSharedCheck_2036_ == 0 {
                                    v_unused_2037_ = lean_ctor_get(v_p_u2081_2008_, 2);
                                    lean_dec(v_unused_2037_);
                                    v_unused_2038_ = lean_ctor_get(v_p_u2081_2008_, 1);
                                    lean_dec(v_unused_2038_);
                                    v_unused_2039_ = lean_ctor_get(v_p_u2081_2008_, 0);
                                    lean_dec(v_unused_2039_);
                                    v___x_2030_ = v_p_u2081_2008_;
                                    v_isShared_2031_ = v_isSharedCheck_2036_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2081_2008_);
                                    v___x_2030_ = lean_box(0);
                                    v_isShared_2031_ = v_isSharedCheck_2036_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_p_2015_);
                            lean_inc(v_k_2013_);
                            lean_inc(v_p_2012_);
                            lean_inc(v_v_2011_);
                            lean_inc(v_k_2010_);
                            lean_dec_ref_known(v_p_u2081_2008_, 3);
                            v_isSharedCheck_2051_ = (!lean_is_exclusive(v_p_u2082_2009_)) as u8;
                            if v_isSharedCheck_2051_ == 0 {
                                v_unused_2052_ = lean_ctor_get(v_p_u2082_2009_, 2);
                                lean_dec(v_unused_2052_);
                                v_unused_2053_ = lean_ctor_get(v_p_u2082_2009_, 1);
                                lean_dec(v_unused_2053_);
                                v_unused_2054_ = lean_ctor_get(v_p_u2082_2009_, 0);
                                lean_dec(v_unused_2054_);
                                v___x_2041_ = v_p_u2082_2009_;
                                v_isShared_2042_ = v_isSharedCheck_2051_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v_p_u2082_2009_);
                                v___x_2041_ = lean_box(0);
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
                    lean_ctor_set(v___x_2019_, 2, v___x_2021_);
                    v___x_2023_ = v___x_2019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_k_2013_);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_v_2014_);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 2, v___x_2021_);
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
                    lean_ctor_set(v___x_2030_, 2, v___x_2032_);
                    v___x_2034_ = v___x_2030_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_k_2010_);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_v_2011_);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 2, v___x_2032_);
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
                lean_dec(v_k_2013_);
                lean_dec(v_k_2010_);
                v___x_2044_ = lean_obj_once(
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
                        lean_ctor_set(v___x_2041_, 2, v___x_2046_);
                        lean_ctor_set(v___x_2041_, 1, v_v_2011_);
                        lean_ctor_set(v___x_2041_, 0, v_a_2043_);
                        v___x_2048_ = v___x_2041_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
                        lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_v_2011_);
                        lean_ctor_set(v_reuseFailAlloc_2049_, 2, v___x_2046_);
                        v___x_2048_ = v_reuseFailAlloc_2049_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2043_);
                    lean_del_object(v___x_2041_);
                    lean_dec(v_v_2011_);
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
    mut v_p_u2081_2055_: *mut LeanObject,
    mut v_p_u2082_2056_: *mut LeanObject,
    mut v_h__1_2057_: *mut LeanObject,
    mut v_h__2_2058_: *mut LeanObject,
    mut v_h__3_2059_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2081_2055_) == 0 {
        let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_2059_);
        lean_dec(v_h__2_2058_);
        v___x_2060_ = lean_apply_1(v_h__1_2057_, v_p_u2082_2056_);
        return v___x_2060_;
    } else {
        lean_dec(v_h__1_2057_);
        if lean_obj_tag(v_p_u2082_2056_) == 0 {
            let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2059_);
            v___x_2061_ = lean_apply_2(v_h__2_2058_, v_p_u2081_2055_, lean_box(0));
            return v___x_2061_;
        } else {
            let mut v_k_2062_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2063_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2064_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2065_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2066_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2067_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2058_);
            v_k_2062_ = lean_ctor_get(v_p_u2081_2055_, 0);
            lean_inc(v_k_2062_);
            v_v_2063_ = lean_ctor_get(v_p_u2081_2055_, 1);
            lean_inc(v_v_2063_);
            v_p_2064_ = lean_ctor_get(v_p_u2081_2055_, 2);
            lean_inc(v_p_2064_);
            lean_dec_ref_known(v_p_u2081_2055_, 3);
            v_k_2065_ = lean_ctor_get(v_p_u2082_2056_, 0);
            lean_inc(v_k_2065_);
            v_v_2066_ = lean_ctor_get(v_p_u2082_2056_, 1);
            lean_inc(v_v_2066_);
            v_p_2067_ = lean_ctor_get(v_p_u2082_2056_, 2);
            lean_inc(v_p_2067_);
            lean_dec_ref_known(v_p_u2082_2056_, 3);
            v___x_2068_ = lean_apply_6(
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
    mut v_motive_2069_: *mut LeanObject,
    mut v_p_u2081_2070_: *mut LeanObject,
    mut v_p_u2082_2071_: *mut LeanObject,
    mut v_h__1_2072_: *mut LeanObject,
    mut v_h__2_2073_: *mut LeanObject,
    mut v_h__3_2074_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2081_2070_) == 0 {
        let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_2074_);
        lean_dec(v_h__2_2073_);
        v___x_2075_ = lean_apply_1(v_h__1_2072_, v_p_u2082_2071_);
        return v___x_2075_;
    } else {
        lean_dec(v_h__1_2072_);
        if lean_obj_tag(v_p_u2082_2071_) == 0 {
            let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2074_);
            v___x_2076_ = lean_apply_2(v_h__2_2073_, v_p_u2081_2070_, lean_box(0));
            return v___x_2076_;
        } else {
            let mut v_k_2077_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2078_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2079_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2080_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2081_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2082_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2073_);
            v_k_2077_ = lean_ctor_get(v_p_u2081_2070_, 0);
            lean_inc(v_k_2077_);
            v_v_2078_ = lean_ctor_get(v_p_u2081_2070_, 1);
            lean_inc(v_v_2078_);
            v_p_2079_ = lean_ctor_get(v_p_u2081_2070_, 2);
            lean_inc(v_p_2079_);
            lean_dec_ref_known(v_p_u2081_2070_, 3);
            v_k_2080_ = lean_ctor_get(v_p_u2082_2071_, 0);
            lean_inc(v_k_2080_);
            v_v_2081_ = lean_ctor_get(v_p_u2082_2071_, 1);
            lean_inc(v_v_2081_);
            v_p_2082_ = lean_ctor_get(v_p_u2082_2071_, 2);
            lean_inc(v_p_2082_);
            lean_dec_ref_known(v_p_u2082_2071_, 3);
            v___x_2083_ = lean_apply_6(
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
    mut v_a_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    v___x_2085_ = lean_nat_to_int(v_a_2084_);
    return v___x_2085_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_toPoly_x27_go(
    mut v_coeff_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: u8 = 0;
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_2087_) {
                0 => {
                    lean_dec(v_coeff_2086_);
                    return v_a_2088_;
                }
                1 => {
                    v_i_2089_ = lean_ctor_get(v_a_2087_, 0);
                    lean_inc(v_i_2089_);
                    lean_dec_ref_known(v_a_2087_, 1);
                    v___x_2090_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2090_, 0, v_coeff_2086_);
                    lean_ctor_set(v___x_2090_, 1, v_i_2089_);
                    lean_ctor_set(v___x_2090_, 2, v_a_2088_);
                    return v___x_2090_;
                }
                2 => {
                    v_a_2091_ = lean_ctor_get(v_a_2087_, 0);
                    lean_inc(v_a_2091_);
                    v_b_2092_ = lean_ctor_get(v_a_2087_, 1);
                    lean_inc(v_b_2092_);
                    lean_dec_ref_known(v_a_2087_, 2);
                    lean_inc(v_coeff_2086_);
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
                    v_a_2095_ = lean_ctor_get(v_a_2087_, 0);
                    lean_inc(v_a_2095_);
                    v_b_2096_ = lean_ctor_get(v_a_2087_, 1);
                    lean_inc(v_b_2096_);
                    lean_dec_ref_known(v_a_2087_, 2);
                    v___x_2097_ = lean_int_neg(v_coeff_2086_);
                    v___x_2098_ =
                        l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_2097_, v_b_2096_, v_a_2088_);
                    v_a_2087_ = v_a_2095_;
                    v_a_2088_ = v___x_2098_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_a_2100_ = lean_ctor_get(v_a_2087_, 0);
                    lean_inc(v_a_2100_);
                    lean_dec_ref_known(v_a_2087_, 1);
                    v___x_2101_ = lean_int_neg(v_coeff_2086_);
                    lean_dec(v_coeff_2086_);
                    v_coeff_2086_ = v___x_2101_;
                    v_a_2087_ = v_a_2100_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_k_2103_ = lean_ctor_get(v_a_2087_, 0);
                    lean_inc(v_k_2103_);
                    v_a_2104_ = lean_ctor_get(v_a_2087_, 1);
                    lean_inc(v_a_2104_);
                    lean_dec_ref_known(v_a_2087_, 2);
                    v___x_2105_ = lean_unsigned_to_nat(0);
                    v___x_2106_ = lean_nat_dec_eq(v_k_2103_, v___x_2105_);
                    if v___x_2106_ == 0 {
                        v___x_2107_ = lean_nat_to_int(v_k_2103_);
                        v___x_2108_ = lean_int_mul(v_coeff_2086_, v___x_2107_);
                        lean_dec(v___x_2107_);
                        lean_dec(v_coeff_2086_);
                        v_coeff_2086_ = v___x_2108_;
                        v_a_2087_ = v_a_2104_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_2104_);
                        lean_dec(v_k_2103_);
                        lean_dec(v_coeff_2086_);
                        return v_a_2088_;
                    }
                }
                _ => {
                    v_k_2110_ = lean_ctor_get(v_a_2087_, 0);
                    lean_inc(v_k_2110_);
                    v_a_2111_ = lean_ctor_get(v_a_2087_, 1);
                    lean_inc(v_a_2111_);
                    lean_dec_ref_known(v_a_2087_, 2);
                    v___x_2112_ = lean_obj_once(
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
                        lean_dec(v_k_2110_);
                        lean_dec(v_coeff_2086_);
                        v_coeff_2086_ = v___x_2114_;
                        v_a_2087_ = v_a_2111_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_2111_);
                        lean_dec(v_k_2110_);
                        lean_dec(v_coeff_2086_);
                        return v_a_2088_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_toPoly_x27(
    mut v_e_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2118_ = lean_box(0);
    v___x_2119_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_2117_, v_e_2116_, v___x_2118_);
    return v___x_2119_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_norm(mut v_e_2120_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_Grind_Linarith_Expr_toPoly_x27(v_e_2120_);
    v___x_2122_ = l_Lean_Grind_Linarith_Poly_norm(v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul_x27(
    mut v_p_2123_: *mut LeanObject,
    mut v_k_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_2123_) == 0 {
                    return v_p_2123_;
                } else {
                    v_k_2125_ = lean_ctor_get(v_p_2123_, 0);
                    v_v_2126_ = lean_ctor_get(v_p_2123_, 1);
                    v_p_2127_ = lean_ctor_get(v_p_2123_, 2);
                    v_isSharedCheck_2136_ = (!lean_is_exclusive(v_p_2123_)) as u8;
                    if v_isSharedCheck_2136_ == 0 {
                        v___x_2129_ = v_p_2123_;
                        v_isShared_2130_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_2127_);
                        lean_inc(v_v_2126_);
                        lean_inc(v_k_2125_);
                        lean_dec(v_p_2123_);
                        v___x_2129_ = lean_box(0);
                        v_isShared_2130_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2131_ = lean_int_mul(v_k_2124_, v_k_2125_);
                lean_dec(v_k_2125_);
                v___x_2132_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_2127_, v_k_2124_);
                if v_isShared_2130_ == 0 {
                    lean_ctor_set(v___x_2129_, 2, v___x_2132_);
                    lean_ctor_set(v___x_2129_, 0, v___x_2131_);
                    v___x_2134_ = v___x_2129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_v_2126_);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 2, v___x_2132_);
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
    mut v_p_2137_: *mut LeanObject,
    mut v_k_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2139_: *mut LeanObject = core::ptr::null_mut();
    v_res_2139_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_2137_, v_k_2138_);
    lean_dec(v_k_2138_);
    return v_res_2139_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul(
    mut v_p_2140_: *mut LeanObject,
    mut v_k_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: u8 = 0;
    v___x_2142_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2143_ = lean_int_dec_eq(v_k_2141_, v___x_2142_);
    if v___x_2143_ == 0 {
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        v___x_2144_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_2140_, v_k_2141_);
        return v___x_2144_;
    } else {
        let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_2140_);
        v___x_2145_ = lean_box(0);
        return v___x_2145_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_mul___boxed(
    mut v_p_2146_: *mut LeanObject,
    mut v_k_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2148_: *mut LeanObject = core::ptr::null_mut();
    v_res_2148_ = l_Lean_Grind_Linarith_Poly_mul(v_p_2146_, v_k_2147_);
    lean_dec(v_k_2147_);
    return v_res_2148_;
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(
    mut v_p_2149_: *mut LeanObject,
    mut v_h__1_2150_: *mut LeanObject,
    mut v_h__2_2151_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_2149_) == 0 {
        let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2151_);
        v___x_2152_ = lean_box(0);
        v___x_2153_ = lean_apply_1(v_h__1_2150_, v___x_2152_);
        return v___x_2153_;
    } else {
        let mut v_k_2154_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_2156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2150_);
        v_k_2154_ = lean_ctor_get(v_p_2149_, 0);
        lean_inc(v_k_2154_);
        v_v_2155_ = lean_ctor_get(v_p_2149_, 1);
        lean_inc(v_v_2155_);
        v_p_2156_ = lean_ctor_get(v_p_2149_, 2);
        lean_inc(v_p_2156_);
        lean_dec_ref_known(v_p_2149_, 3);
        v___x_2157_ = lean_apply_3(v_h__2_2151_, v_k_2154_, v_v_2155_, v_p_2156_);
        return v___x_2157_;
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(
    mut v_motive_2158_: *mut LeanObject,
    mut v_p_2159_: *mut LeanObject,
    mut v_h__1_2160_: *mut LeanObject,
    mut v_h__2_2161_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_2159_) == 0 {
        let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2161_);
        v___x_2162_ = lean_box(0);
        v___x_2163_ = lean_apply_1(v_h__1_2160_, v___x_2162_);
        return v___x_2163_;
    } else {
        let mut v_k_2164_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_2165_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_2166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2160_);
        v_k_2164_ = lean_ctor_get(v_p_2159_, 0);
        lean_inc(v_k_2164_);
        v_v_2165_ = lean_ctor_get(v_p_2159_, 1);
        lean_inc(v_v_2165_);
        v_p_2166_ = lean_ctor_get(v_p_2159_, 2);
        lean_inc(v_p_2166_);
        lean_dec_ref_known(v_p_2159_, 3);
        v___x_2167_ = lean_apply_3(v_h__2_2161_, v_k_2164_, v_v_2165_, v_p_2166_);
        return v___x_2167_;
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(
    mut v_x_2168_: *mut LeanObject,
    mut v_h__1_2169_: *mut LeanObject,
    mut v_h__2_2170_: *mut LeanObject,
    mut v_h__3_2171_: *mut LeanObject,
    mut v_h__4_2172_: *mut LeanObject,
    mut v_h__5_2173_: *mut LeanObject,
    mut v_h__6_2174_: *mut LeanObject,
    mut v_h__7_2175_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2168_) {
        0 => {
            let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2175_);
            lean_dec(v_h__6_2174_);
            lean_dec(v_h__5_2173_);
            lean_dec(v_h__4_2172_);
            lean_dec(v_h__3_2171_);
            lean_dec(v_h__2_2170_);
            v___x_2176_ = lean_box(0);
            v___x_2177_ = lean_apply_1(v_h__1_2169_, v___x_2176_);
            return v___x_2177_;
        }
        1 => {
            let mut v_i_2178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2175_);
            lean_dec(v_h__6_2174_);
            lean_dec(v_h__5_2173_);
            lean_dec(v_h__4_2172_);
            lean_dec(v_h__3_2171_);
            lean_dec(v_h__1_2169_);
            v_i_2178_ = lean_ctor_get(v_x_2168_, 0);
            lean_inc(v_i_2178_);
            lean_dec_ref_known(v_x_2168_, 1);
            v___x_2179_ = lean_apply_1(v_h__2_2170_, v_i_2178_);
            return v___x_2179_;
        }
        2 => {
            let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_2181_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2175_);
            lean_dec(v_h__6_2174_);
            lean_dec(v_h__5_2173_);
            lean_dec(v_h__4_2172_);
            lean_dec(v_h__2_2170_);
            lean_dec(v_h__1_2169_);
            v_a_2180_ = lean_ctor_get(v_x_2168_, 0);
            lean_inc(v_a_2180_);
            v_b_2181_ = lean_ctor_get(v_x_2168_, 1);
            lean_inc(v_b_2181_);
            lean_dec_ref_known(v_x_2168_, 2);
            v___x_2182_ = lean_apply_2(v_h__3_2171_, v_a_2180_, v_b_2181_);
            return v___x_2182_;
        }
        3 => {
            let mut v_a_2183_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_2184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2175_);
            lean_dec(v_h__6_2174_);
            lean_dec(v_h__5_2173_);
            lean_dec(v_h__3_2171_);
            lean_dec(v_h__2_2170_);
            lean_dec(v_h__1_2169_);
            v_a_2183_ = lean_ctor_get(v_x_2168_, 0);
            lean_inc(v_a_2183_);
            v_b_2184_ = lean_ctor_get(v_x_2168_, 1);
            lean_inc(v_b_2184_);
            lean_dec_ref_known(v_x_2168_, 2);
            v___x_2185_ = lean_apply_2(v_h__4_2172_, v_a_2183_, v_b_2184_);
            return v___x_2185_;
        }
        4 => {
            let mut v_a_2186_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_2174_);
            lean_dec(v_h__5_2173_);
            lean_dec(v_h__4_2172_);
            lean_dec(v_h__3_2171_);
            lean_dec(v_h__2_2170_);
            lean_dec(v_h__1_2169_);
            v_a_2186_ = lean_ctor_get(v_x_2168_, 0);
            lean_inc(v_a_2186_);
            lean_dec_ref_known(v_x_2168_, 1);
            v___x_2187_ = lean_apply_1(v_h__7_2175_, v_a_2186_);
            return v___x_2187_;
        }
        5 => {
            let mut v_k_2188_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2189_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2175_);
            lean_dec(v_h__6_2174_);
            lean_dec(v_h__4_2172_);
            lean_dec(v_h__3_2171_);
            lean_dec(v_h__2_2170_);
            lean_dec(v_h__1_2169_);
            v_k_2188_ = lean_ctor_get(v_x_2168_, 0);
            lean_inc(v_k_2188_);
            v_a_2189_ = lean_ctor_get(v_x_2168_, 1);
            lean_inc(v_a_2189_);
            lean_dec_ref_known(v_x_2168_, 2);
            v___x_2190_ = lean_apply_2(v_h__5_2173_, v_k_2188_, v_a_2189_);
            return v___x_2190_;
        }
        _ => {
            let mut v_k_2191_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2175_);
            lean_dec(v_h__5_2173_);
            lean_dec(v_h__4_2172_);
            lean_dec(v_h__3_2171_);
            lean_dec(v_h__2_2170_);
            lean_dec(v_h__1_2169_);
            v_k_2191_ = lean_ctor_get(v_x_2168_, 0);
            lean_inc(v_k_2191_);
            v_a_2192_ = lean_ctor_get(v_x_2168_, 1);
            lean_inc(v_a_2192_);
            lean_dec_ref_known(v_x_2168_, 2);
            v___x_2193_ = lean_apply_2(v_h__6_2174_, v_k_2191_, v_a_2192_);
            return v___x_2193_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(
    mut v_motive_2194_: *mut LeanObject,
    mut v_x_2195_: *mut LeanObject,
    mut v_h__1_2196_: *mut LeanObject,
    mut v_h__2_2197_: *mut LeanObject,
    mut v_h__3_2198_: *mut LeanObject,
    mut v_h__4_2199_: *mut LeanObject,
    mut v_h__5_2200_: *mut LeanObject,
    mut v_h__6_2201_: *mut LeanObject,
    mut v_h__7_2202_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2195_) {
        0 => {
            let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2202_);
            lean_dec(v_h__6_2201_);
            lean_dec(v_h__5_2200_);
            lean_dec(v_h__4_2199_);
            lean_dec(v_h__3_2198_);
            lean_dec(v_h__2_2197_);
            v___x_2203_ = lean_box(0);
            v___x_2204_ = lean_apply_1(v_h__1_2196_, v___x_2203_);
            return v___x_2204_;
        }
        1 => {
            let mut v_i_2205_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2202_);
            lean_dec(v_h__6_2201_);
            lean_dec(v_h__5_2200_);
            lean_dec(v_h__4_2199_);
            lean_dec(v_h__3_2198_);
            lean_dec(v_h__1_2196_);
            v_i_2205_ = lean_ctor_get(v_x_2195_, 0);
            lean_inc(v_i_2205_);
            lean_dec_ref_known(v_x_2195_, 1);
            v___x_2206_ = lean_apply_1(v_h__2_2197_, v_i_2205_);
            return v___x_2206_;
        }
        2 => {
            let mut v_a_2207_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_2208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2202_);
            lean_dec(v_h__6_2201_);
            lean_dec(v_h__5_2200_);
            lean_dec(v_h__4_2199_);
            lean_dec(v_h__2_2197_);
            lean_dec(v_h__1_2196_);
            v_a_2207_ = lean_ctor_get(v_x_2195_, 0);
            lean_inc(v_a_2207_);
            v_b_2208_ = lean_ctor_get(v_x_2195_, 1);
            lean_inc(v_b_2208_);
            lean_dec_ref_known(v_x_2195_, 2);
            v___x_2209_ = lean_apply_2(v_h__3_2198_, v_a_2207_, v_b_2208_);
            return v___x_2209_;
        }
        3 => {
            let mut v_a_2210_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_2211_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2202_);
            lean_dec(v_h__6_2201_);
            lean_dec(v_h__5_2200_);
            lean_dec(v_h__3_2198_);
            lean_dec(v_h__2_2197_);
            lean_dec(v_h__1_2196_);
            v_a_2210_ = lean_ctor_get(v_x_2195_, 0);
            lean_inc(v_a_2210_);
            v_b_2211_ = lean_ctor_get(v_x_2195_, 1);
            lean_inc(v_b_2211_);
            lean_dec_ref_known(v_x_2195_, 2);
            v___x_2212_ = lean_apply_2(v_h__4_2199_, v_a_2210_, v_b_2211_);
            return v___x_2212_;
        }
        4 => {
            let mut v_a_2213_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_2201_);
            lean_dec(v_h__5_2200_);
            lean_dec(v_h__4_2199_);
            lean_dec(v_h__3_2198_);
            lean_dec(v_h__2_2197_);
            lean_dec(v_h__1_2196_);
            v_a_2213_ = lean_ctor_get(v_x_2195_, 0);
            lean_inc(v_a_2213_);
            lean_dec_ref_known(v_x_2195_, 1);
            v___x_2214_ = lean_apply_1(v_h__7_2202_, v_a_2213_);
            return v___x_2214_;
        }
        5 => {
            let mut v_k_2215_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2202_);
            lean_dec(v_h__6_2201_);
            lean_dec(v_h__4_2199_);
            lean_dec(v_h__3_2198_);
            lean_dec(v_h__2_2197_);
            lean_dec(v_h__1_2196_);
            v_k_2215_ = lean_ctor_get(v_x_2195_, 0);
            lean_inc(v_k_2215_);
            v_a_2216_ = lean_ctor_get(v_x_2195_, 1);
            lean_inc(v_a_2216_);
            lean_dec_ref_known(v_x_2195_, 2);
            v___x_2217_ = lean_apply_2(v_h__5_2200_, v_k_2215_, v_a_2216_);
            return v___x_2217_;
        }
        _ => {
            let mut v_k_2218_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_2202_);
            lean_dec(v_h__5_2200_);
            lean_dec(v_h__4_2199_);
            lean_dec(v_h__3_2198_);
            lean_dec(v_h__2_2197_);
            lean_dec(v_h__1_2196_);
            v_k_2218_ = lean_ctor_get(v_x_2195_, 0);
            lean_inc(v_k_2218_);
            v_a_2219_ = lean_ctor_get(v_x_2195_, 1);
            lean_inc(v_a_2219_);
            lean_dec_ref_known(v_x_2195_, 2);
            v___x_2220_ = lean_apply_2(v_h__6_2201_, v_k_2218_, v_a_2219_);
            return v___x_2220_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_leadCoeff(
    mut v_p_2221_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_2221_) == 1 {
        let mut v_k_2222_: *mut LeanObject = core::ptr::null_mut();
        v_k_2222_ = lean_ctor_get(v_p_2221_, 0);
        lean_inc(v_k_2222_);
        return v_k_2222_;
    } else {
        let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
        v___x_2223_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
            _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
        );
        return v___x_2223_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(
    mut v_p_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2225_: *mut LeanObject = core::ptr::null_mut();
    v_res_2225_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_2224_);
    lean_dec(v_p_2224_);
    return v_res_2225_;
}
pub unsafe fn l_Lean_Grind_Linarith_le__le__combine__cert(
    mut v_p_u2081_2226_: *mut LeanObject,
    mut v_p_u2082_2227_: *mut LeanObject,
    mut v_p_u2083_2228_: *mut LeanObject,
) -> u8 {
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2082_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    v___x_2229_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_2226_);
    v_a_u2081_2230_ = lean_nat_abs(v___x_2229_);
    lean_dec(v___x_2229_);
    v___x_2231_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_2227_);
    v_a_u2082_2232_ = lean_nat_abs(v___x_2231_);
    lean_dec(v___x_2231_);
    v___x_2233_ = lean_nat_to_int(v_a_u2082_2232_);
    v___x_2234_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2226_, v___x_2233_);
    lean_dec(v___x_2233_);
    v___x_2235_ = lean_nat_to_int(v_a_u2081_2230_);
    v___x_2236_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2227_, v___x_2235_);
    lean_dec(v___x_2235_);
    v___x_2237_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2234_, v___x_2236_);
    v___x_2238_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2228_, v___x_2237_);
    lean_dec(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_Grind_Linarith_le__le__combine__cert___boxed(
    mut v_p_u2081_2239_: *mut LeanObject,
    mut v_p_u2082_2240_: *mut LeanObject,
    mut v_p_u2083_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2242_: u8 = 0;
    let mut v_r_2243_: *mut LeanObject = core::ptr::null_mut();
    v_res_2242_ = l_Lean_Grind_Linarith_le__le__combine__cert(
        v_p_u2081_2239_,
        v_p_u2082_2240_,
        v_p_u2083_2241_,
    );
    lean_dec(v_p_u2083_2241_);
    v_r_2243_ = lean_box((v_res_2242_) as usize);
    return v_r_2243_;
}
pub unsafe fn l_Lean_Grind_Linarith_le__lt__combine__cert(
    mut v_p_u2081_2244_: *mut LeanObject,
    mut v_p_u2082_2245_: *mut LeanObject,
    mut v_p_u2083_2246_: *mut LeanObject,
) -> u8 {
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    v___x_2247_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_2244_);
    v_a_u2081_2248_ = lean_nat_abs(v___x_2247_);
    lean_dec(v___x_2247_);
    v___x_2249_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2250_ = lean_nat_to_int(v_a_u2081_2248_);
    v___x_2251_ = lean_int_dec_lt(v___x_2249_, v___x_2250_);
    if v___x_2251_ == 0 {
        lean_dec(v___x_2250_);
        lean_dec(v_p_u2082_2245_);
        lean_dec(v_p_u2081_2244_);
        return v___x_2251_;
    } else {
        let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_u2082_2253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: u8 = 0;
        v___x_2252_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_2245_);
        v_a_u2082_2253_ = lean_nat_abs(v___x_2252_);
        lean_dec(v___x_2252_);
        v___x_2254_ = lean_nat_to_int(v_a_u2082_2253_);
        v___x_2255_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2244_, v___x_2254_);
        lean_dec(v___x_2254_);
        v___x_2256_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2245_, v___x_2250_);
        lean_dec(v___x_2250_);
        v___x_2257_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2255_, v___x_2256_);
        v___x_2258_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2246_, v___x_2257_);
        lean_dec(v___x_2257_);
        return v___x_2258_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(
    mut v_p_u2081_2259_: *mut LeanObject,
    mut v_p_u2082_2260_: *mut LeanObject,
    mut v_p_u2083_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2262_: u8 = 0;
    let mut v_r_2263_: *mut LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Lean_Grind_Linarith_le__lt__combine__cert(
        v_p_u2081_2259_,
        v_p_u2082_2260_,
        v_p_u2083_2261_,
    );
    lean_dec(v_p_u2083_2261_);
    v_r_2263_ = lean_box((v_res_2262_) as usize);
    return v_r_2263_;
}
pub unsafe fn l_Lean_Grind_Linarith_lt__lt__combine__cert(
    mut v_p_u2081_2264_: *mut LeanObject,
    mut v_p_u2082_2265_: *mut LeanObject,
    mut v_p_u2083_2266_: *mut LeanObject,
) -> u8 {
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2082_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: u8 = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2267_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_2264_);
                v_a_u2081_2268_ = lean_nat_abs(v___x_2267_);
                lean_dec(v___x_2267_);
                v___x_2269_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_2265_);
                v_a_u2082_2270_ = lean_nat_abs(v___x_2269_);
                lean_dec(v___x_2269_);
                v___x_2279_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once
                    ),
                    _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
                );
                lean_inc(v_a_u2082_2270_);
                v___x_2280_ = lean_nat_to_int(v_a_u2082_2270_);
                v___x_2281_ = lean_int_dec_lt(v___x_2279_, v___x_2280_);
                lean_dec(v___x_2280_);
                if v___x_2281_ == 0 {
                    v___y_2272_ = v___x_2281_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_u2081_2268_);
                    v___x_2282_ = lean_nat_to_int(v_a_u2081_2268_);
                    v___x_2283_ = lean_int_dec_lt(v___x_2279_, v___x_2282_);
                    lean_dec(v___x_2282_);
                    v___y_2272_ = v___x_2283_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2272_ == 0 {
                    lean_dec(v_a_u2082_2270_);
                    lean_dec(v_a_u2081_2268_);
                    lean_dec(v_p_u2082_2265_);
                    lean_dec(v_p_u2081_2264_);
                    return v___y_2272_;
                } else {
                    v___x_2273_ = lean_nat_to_int(v_a_u2082_2270_);
                    v___x_2274_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2264_, v___x_2273_);
                    lean_dec(v___x_2273_);
                    v___x_2275_ = lean_nat_to_int(v_a_u2081_2268_);
                    v___x_2276_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2265_, v___x_2275_);
                    lean_dec(v___x_2275_);
                    v___x_2277_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2274_, v___x_2276_);
                    v___x_2278_ =
                        l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2266_, v___x_2277_);
                    lean_dec(v___x_2277_);
                    return v___x_2278_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(
    mut v_p_u2081_2284_: *mut LeanObject,
    mut v_p_u2082_2285_: *mut LeanObject,
    mut v_p_u2083_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2287_: u8 = 0;
    let mut v_r_2288_: *mut LeanObject = core::ptr::null_mut();
    v_res_2287_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(
        v_p_u2081_2284_,
        v_p_u2082_2285_,
        v_p_u2083_2286_,
    );
    lean_dec(v_p_u2083_2286_);
    v_r_2288_ = lean_box((v_res_2287_) as usize);
    return v_r_2288_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0() -> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    v___x_2289_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2290_ = lean_int_neg(v___x_2289_);
    return v___x_2290_;
}
pub unsafe fn l_Lean_Grind_Linarith_diseq__split__cert(
    mut v_p_u2081_2291_: *mut LeanObject,
    mut v_p_u2082_2292_: *mut LeanObject,
) -> u8 {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    v___x_2293_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2294_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2291_, v___x_2293_);
    v___x_2295_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_2292_, v___x_2294_);
    lean_dec(v___x_2294_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_Grind_Linarith_diseq__split__cert___boxed(
    mut v_p_u2081_2296_: *mut LeanObject,
    mut v_p_u2082_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2298_: u8 = 0;
    let mut v_r_2299_: *mut LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_2296_, v_p_u2082_2297_);
    lean_dec(v_p_u2082_2297_);
    v_r_2299_ = lean_box((v_res_2298_) as usize);
    return v_r_2299_;
}
pub unsafe fn l_Lean_Grind_Linarith_norm__cert(
    mut v_lhs_2300_: *mut LeanObject,
    mut v_rhs_2301_: *mut LeanObject,
    mut v_p_2302_: *mut LeanObject,
) -> u8 {
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    v___x_2303_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2303_, 0, v_lhs_2300_);
    lean_ctor_set(v___x_2303_, 1, v_rhs_2301_);
    v___x_2304_ = l_Lean_Grind_Linarith_Expr_norm(v___x_2303_);
    v___x_2305_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2302_, v___x_2304_);
    lean_dec(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn l_Lean_Grind_Linarith_norm__cert___boxed(
    mut v_lhs_2306_: *mut LeanObject,
    mut v_rhs_2307_: *mut LeanObject,
    mut v_p_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2309_: u8 = 0;
    let mut v_r_2310_: *mut LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Lean_Grind_Linarith_norm__cert(v_lhs_2306_, v_rhs_2307_, v_p_2308_);
    lean_dec(v_p_2308_);
    v_r_2310_ = lean_box((v_res_2309_) as usize);
    return v_r_2310_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__of__le__ge__cert(
    mut v_p_u2081_2311_: *mut LeanObject,
    mut v_p_u2082_2312_: *mut LeanObject,
) -> u8 {
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: u8 = 0;
    v___x_2313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2314_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2311_, v___x_2313_);
    v___x_2315_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_2312_, v___x_2314_);
    lean_dec(v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(
    mut v_p_u2081_2316_: *mut LeanObject,
    mut v_p_u2082_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2318_: u8 = 0;
    let mut v_r_2319_: *mut LeanObject = core::ptr::null_mut();
    v_res_2318_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_2316_, v_p_u2082_2317_);
    lean_dec(v_p_u2082_2317_);
    v_r_2319_ = lean_box((v_res_2318_) as usize);
    return v_r_2319_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0() -> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    v___x_2320_ = lean_box(0);
    v___x_2321_ = lean_unsigned_to_nat(0);
    v___x_2322_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2323_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2323_, 0, v___x_2322_);
    lean_ctor_set(v___x_2323_, 1, v___x_2321_);
    lean_ctor_set(v___x_2323_, 2, v___x_2320_);
    return v___x_2323_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__lt__one__cert(mut v_p_2324_: *mut LeanObject) -> u8 {
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    v___x_2325_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0,
    );
    v___x_2326_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2324_, v___x_2325_);
    return v___x_2326_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(
    mut v_p_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2328_: u8 = 0;
    let mut v_r_2329_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_2327_);
    lean_dec(v_p_2327_);
    v_r_2329_ = lean_box((v_res_2328_) as usize);
    return v_r_2329_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0() -> *mut LeanObject {
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    v___x_2330_ = lean_box(0);
    v___x_2331_ = lean_unsigned_to_nat(0);
    v___x_2332_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2333_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    lean_ctor_set(v___x_2333_, 1, v___x_2331_);
    lean_ctor_set(v___x_2333_, 2, v___x_2330_);
    return v___x_2333_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__cert(mut v_p_2334_: *mut LeanObject) -> u8 {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    v___x_2335_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0,
    );
    v___x_2336_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2334_, v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(
    mut v_p_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: u8 = 0;
    let mut v_r_2339_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_2337_);
    lean_dec(v_p_2337_);
    v_r_2339_ = lean_box((v_res_2338_) as usize);
    return v_r_2339_;
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(
    mut v_c_2340_: *mut LeanObject,
    mut v_p_2341_: *mut LeanObject,
) -> u8 {
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    v___x_2342_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2343_ = lean_nat_to_int(v_c_2340_);
    v___x_2344_ = lean_int_dec_lt(v___x_2342_, v___x_2343_);
    lean_dec(v___x_2343_);
    if v___x_2344_ == 0 {
        return v___x_2344_;
    } else {
        let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: u8 = 0;
        v___x_2345_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once),
            _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0,
        );
        v___x_2346_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2341_, v___x_2345_);
        return v___x_2346_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(
    mut v_c_2347_: *mut LeanObject,
    mut v_p_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2349_: u8 = 0;
    let mut v_r_2350_: *mut LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_2347_, v_p_2348_);
    lean_dec(v_p_2348_);
    v_r_2350_ = lean_box((v_res_2349_) as usize);
    return v_r_2350_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__neg__cert(
    mut v_p_u2081_2351_: *mut LeanObject,
    mut v_p_u2082_2352_: *mut LeanObject,
) -> u8 {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    v___x_2353_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2354_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2351_, v___x_2353_);
    v___x_2355_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_2352_, v___x_2354_);
    lean_dec(v___x_2354_);
    return v___x_2355_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__neg__cert___boxed(
    mut v_p_u2081_2356_: *mut LeanObject,
    mut v_p_u2082_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2358_: u8 = 0;
    let mut v_r_2359_: *mut LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_2356_, v_p_u2082_2357_);
    lean_dec(v_p_u2082_2357_);
    v_r_2359_ = lean_box((v_res_2358_) as usize);
    return v_r_2359_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__coeff__cert(
    mut v_p_u2081_2360_: *mut LeanObject,
    mut v_p_u2082_2361_: *mut LeanObject,
    mut v_k_2362_: *mut LeanObject,
) -> u8 {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: u8 = 0;
    v___x_2363_ = lean_unsigned_to_nat(0);
    v___x_2364_ = lean_nat_dec_eq(v_k_2362_, v___x_2363_);
    if v___x_2364_ == 0 {
        let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: u8 = 0;
        v___x_2365_ = lean_nat_to_int(v_k_2362_);
        v___x_2366_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2361_, v___x_2365_);
        lean_dec(v___x_2365_);
        v___x_2367_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_2360_, v___x_2366_);
        lean_dec(v___x_2366_);
        return v___x_2367_;
    } else {
        let mut v___x_2368_: u8 = 0;
        lean_dec(v_k_2362_);
        lean_dec(v_p_u2082_2361_);
        v___x_2368_ = 0;
        return v___x_2368_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__coeff__cert___boxed(
    mut v_p_u2081_2369_: *mut LeanObject,
    mut v_p_u2082_2370_: *mut LeanObject,
    mut v_k_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2372_: u8 = 0;
    let mut v_r_2373_: *mut LeanObject = core::ptr::null_mut();
    v_res_2372_ =
        l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_2369_, v_p_u2082_2370_, v_k_2371_);
    lean_dec(v_p_u2081_2369_);
    v_r_2373_ = lean_box((v_res_2372_) as usize);
    return v_r_2373_;
}
pub unsafe fn l_Lean_Grind_Linarith_coeff__cert(
    mut v_p_u2081_2374_: *mut LeanObject,
    mut v_p_u2082_2375_: *mut LeanObject,
    mut v_k_2376_: *mut LeanObject,
) -> u8 {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    v___x_2377_ = lean_unsigned_to_nat(0);
    v___x_2378_ = lean_nat_dec_lt(v___x_2377_, v_k_2376_);
    if v___x_2378_ == 0 {
        lean_dec(v_k_2376_);
        lean_dec(v_p_u2082_2375_);
        return v___x_2378_;
    } else {
        let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2381_: u8 = 0;
        v___x_2379_ = lean_nat_to_int(v_k_2376_);
        v___x_2380_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2375_, v___x_2379_);
        lean_dec(v___x_2379_);
        v___x_2381_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_2374_, v___x_2380_);
        lean_dec(v___x_2380_);
        return v___x_2381_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_coeff__cert___boxed(
    mut v_p_u2081_2382_: *mut LeanObject,
    mut v_p_u2082_2383_: *mut LeanObject,
    mut v_k_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2385_: u8 = 0;
    let mut v_r_2386_: *mut LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_2382_, v_p_u2082_2383_, v_k_2384_);
    lean_dec(v_p_u2081_2382_);
    v_r_2386_ = lean_box((v_res_2385_) as usize);
    return v_r_2386_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst__cert(
    mut v_k_u2081_2387_: *mut LeanObject,
    mut v_k_u2082_2388_: *mut LeanObject,
    mut v_p_u2081_2389_: *mut LeanObject,
    mut v_p_u2082_2390_: *mut LeanObject,
    mut v_p_u2083_2391_: *mut LeanObject,
) -> u8 {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    v___x_2392_ = lean_nat_abs(v_k_u2081_2387_);
    v___x_2393_ = lean_unsigned_to_nat(0);
    v___x_2394_ = lean_nat_dec_eq(v___x_2392_, v___x_2393_);
    lean_dec(v___x_2392_);
    if v___x_2394_ == 0 {
        let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: u8 = 0;
        v___x_2395_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2389_, v_k_u2082_2388_);
        v___x_2396_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2390_, v_k_u2081_2387_);
        v___x_2397_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2395_, v___x_2396_);
        v___x_2398_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2391_, v___x_2397_);
        lean_dec(v___x_2397_);
        return v___x_2398_;
    } else {
        let mut v___x_2399_: u8 = 0;
        lean_dec(v_p_u2082_2390_);
        lean_dec(v_p_u2081_2389_);
        v___x_2399_ = 0;
        return v___x_2399_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(
    mut v_k_u2081_2400_: *mut LeanObject,
    mut v_k_u2082_2401_: *mut LeanObject,
    mut v_p_u2081_2402_: *mut LeanObject,
    mut v_p_u2082_2403_: *mut LeanObject,
    mut v_p_u2083_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2405_: u8 = 0;
    let mut v_r_2406_: *mut LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(
        v_k_u2081_2400_,
        v_k_u2082_2401_,
        v_p_u2081_2402_,
        v_p_u2082_2403_,
        v_p_u2083_2404_,
    );
    lean_dec(v_p_u2083_2404_);
    lean_dec(v_k_u2082_2401_);
    lean_dec(v_k_u2081_2400_);
    v_r_2406_ = lean_box((v_res_2405_) as usize);
    return v_r_2406_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst1__cert(
    mut v_k_2407_: *mut LeanObject,
    mut v_p_u2081_2408_: *mut LeanObject,
    mut v_p_u2082_2409_: *mut LeanObject,
    mut v_p_u2083_2410_: *mut LeanObject,
) -> u8 {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    v___x_2411_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2408_, v_k_2407_);
    v___x_2412_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2411_, v_p_u2082_2409_);
    v___x_2413_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2410_, v___x_2412_);
    lean_dec(v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(
    mut v_k_2414_: *mut LeanObject,
    mut v_p_u2081_2415_: *mut LeanObject,
    mut v_p_u2082_2416_: *mut LeanObject,
    mut v_p_u2083_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: u8 = 0;
    let mut v_r_2419_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(
        v_k_2414_,
        v_p_u2081_2415_,
        v_p_u2082_2416_,
        v_p_u2083_2417_,
    );
    lean_dec(v_p_u2083_2417_);
    lean_dec(v_k_2414_);
    v_r_2419_ = lean_box((v_res_2418_) as usize);
    return v_r_2419_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__le__subst__cert(
    mut v_x_2420_: *mut LeanObject,
    mut v_p_u2081_2421_: *mut LeanObject,
    mut v_p_u2082_2422_: *mut LeanObject,
    mut v_p_u2083_2423_: *mut LeanObject,
) -> u8 {
    let mut v_a_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    v_a_2424_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_2421_, v_x_2420_);
    v___x_2425_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2426_ = lean_int_dec_le(v___x_2425_, v_a_2424_);
    if v___x_2426_ == 0 {
        lean_dec(v_a_2424_);
        lean_dec(v_p_u2082_2422_);
        lean_dec(v_p_u2081_2421_);
        return v___x_2426_;
    } else {
        let mut v_b_2427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: u8 = 0;
        v_b_2427_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_2422_, v_x_2420_);
        v___x_2428_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2422_, v_a_2424_);
        lean_dec(v_a_2424_);
        v___x_2429_ = lean_int_neg(v_b_2427_);
        lean_dec(v_b_2427_);
        v___x_2430_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2421_, v___x_2429_);
        lean_dec(v___x_2429_);
        v___x_2431_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2428_, v___x_2430_);
        v___x_2432_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2423_, v___x_2431_);
        lean_dec(v___x_2431_);
        return v___x_2432_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(
    mut v_x_2433_: *mut LeanObject,
    mut v_p_u2081_2434_: *mut LeanObject,
    mut v_p_u2082_2435_: *mut LeanObject,
    mut v_p_u2083_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2437_: u8 = 0;
    let mut v_r_2438_: *mut LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Lean_Grind_Linarith_eq__le__subst__cert(
        v_x_2433_,
        v_p_u2081_2434_,
        v_p_u2082_2435_,
        v_p_u2083_2436_,
    );
    lean_dec(v_p_u2083_2436_);
    lean_dec(v_x_2433_);
    v_r_2438_ = lean_box((v_res_2437_) as usize);
    return v_r_2438_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__lt__subst__cert(
    mut v_x_2439_: *mut LeanObject,
    mut v_p_u2081_2440_: *mut LeanObject,
    mut v_p_u2082_2441_: *mut LeanObject,
    mut v_p_u2083_2442_: *mut LeanObject,
) -> u8 {
    let mut v_a_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    v_a_2443_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_2440_, v_x_2439_);
    v___x_2444_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22,
    );
    v___x_2445_ = lean_int_dec_lt(v___x_2444_, v_a_2443_);
    if v___x_2445_ == 0 {
        lean_dec(v_a_2443_);
        lean_dec(v_p_u2082_2441_);
        lean_dec(v_p_u2081_2440_);
        return v___x_2445_;
    } else {
        let mut v_b_2446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: u8 = 0;
        v_b_2446_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_2441_, v_x_2439_);
        v___x_2447_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2441_, v_a_2443_);
        lean_dec(v_a_2443_);
        v___x_2448_ = lean_int_neg(v_b_2446_);
        lean_dec(v_b_2446_);
        v___x_2449_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2440_, v___x_2448_);
        lean_dec(v___x_2448_);
        v___x_2450_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2447_, v___x_2449_);
        v___x_2451_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2442_, v___x_2450_);
        lean_dec(v___x_2450_);
        return v___x_2451_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(
    mut v_x_2452_: *mut LeanObject,
    mut v_p_u2081_2453_: *mut LeanObject,
    mut v_p_u2082_2454_: *mut LeanObject,
    mut v_p_u2083_2455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2456_: u8 = 0;
    let mut v_r_2457_: *mut LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(
        v_x_2452_,
        v_p_u2081_2453_,
        v_p_u2082_2454_,
        v_p_u2083_2455_,
    );
    lean_dec(v_p_u2083_2455_);
    lean_dec(v_x_2452_);
    v_r_2457_ = lean_box((v_res_2456_) as usize);
    return v_r_2457_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__eq__subst__cert(
    mut v_x_2458_: *mut LeanObject,
    mut v_p_u2081_2459_: *mut LeanObject,
    mut v_p_u2082_2460_: *mut LeanObject,
    mut v_p_u2083_2461_: *mut LeanObject,
) -> u8 {
    let mut v_a_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u8 = 0;
    v_a_2462_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_2459_, v_x_2458_);
    v_b_2463_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_2460_, v_x_2458_);
    v___x_2464_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_2460_, v_a_2462_);
    lean_dec(v_a_2462_);
    v___x_2465_ = lean_int_neg(v_b_2463_);
    lean_dec(v_b_2463_);
    v___x_2466_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_2459_, v___x_2465_);
    lean_dec(v___x_2465_);
    v___x_2467_ = l_Lean_Grind_Linarith_Poly_combine(v___x_2464_, v___x_2466_);
    v___x_2468_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_2461_, v___x_2467_);
    lean_dec(v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(
    mut v_x_2469_: *mut LeanObject,
    mut v_p_u2081_2470_: *mut LeanObject,
    mut v_p_u2082_2471_: *mut LeanObject,
    mut v_p_u2083_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2473_: u8 = 0;
    let mut v_r_2474_: *mut LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(
        v_x_2469_,
        v_p_u2081_2470_,
        v_p_u2082_2471_,
        v_p_u2083_2472_,
    );
    lean_dec(v_p_u2083_2472_);
    lean_dec(v_x_2469_);
    v_r_2474_ = lean_box((v_res_2473_) as usize);
    return v_r_2474_;
}
pub unsafe fn l_Lean_Grind_Linarith_imp__eq__cert(
    mut v_p_2475_: *mut LeanObject,
    mut v_x_2476_: *mut LeanObject,
    mut v_y_2477_: *mut LeanObject,
) -> u8 {
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    v___x_2478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once),
        _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3,
    );
    v___x_2479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once),
        _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0,
    );
    v___x_2480_ = lean_box(0);
    v___x_2481_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2481_, 0, v___x_2479_);
    lean_ctor_set(v___x_2481_, 1, v_y_2477_);
    lean_ctor_set(v___x_2481_, 2, v___x_2480_);
    v___x_2482_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2482_, 0, v___x_2478_);
    lean_ctor_set(v___x_2482_, 1, v_x_2476_);
    lean_ctor_set(v___x_2482_, 2, v___x_2481_);
    v___x_2483_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_2475_, v___x_2482_);
    lean_dec_ref_known(v___x_2482_, 3);
    return v___x_2483_;
}
pub unsafe fn l_Lean_Grind_Linarith_imp__eq__cert___boxed(
    mut v_p_2484_: *mut LeanObject,
    mut v_x_2485_: *mut LeanObject,
    mut v_y_2486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2487_: u8 = 0;
    let mut v_r_2488_: *mut LeanObject = core::ptr::null_mut();
    v_res_2487_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_2484_, v_x_2485_, v_y_2486_);
    lean_dec(v_p_2484_);
    v_r_2488_ = lean_box((v_res_2487_) as usize);
    return v_r_2488_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ordered_Linarith(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Field(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
    l_Lean_Grind_Linarith_instInhabitedExpr_default =
        _init_l_Lean_Grind_Linarith_instInhabitedExpr_default();
    lean_mark_persistent(l_Lean_Grind_Linarith_instInhabitedExpr_default);
    l_Lean_Grind_Linarith_instInhabitedExpr = _init_l_Lean_Grind_Linarith_instInhabitedExpr();
    lean_mark_persistent(l_Lean_Grind_Linarith_instInhabitedExpr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ordered_Linarith(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Ordered_Linarith(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Field(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ordered_Linarith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Ordered_Linarith(builtin);
}
