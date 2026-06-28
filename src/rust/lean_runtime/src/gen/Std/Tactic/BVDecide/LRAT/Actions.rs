// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Actions
// Imports: Std.Sat.CNF
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_instRepr___redArg___lam__0___boxed, l_Array_isEqvAux___redArg, l_Array_repr___redArg,
};
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___boxed, l_Nat_reprFast, l_Prod_repr___boxed, l_Prod_repr___redArg,
    l_Repr_addAppParen, l_instReprNat___lam__0___boxed, l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringProd___redArg___lam__0;
use crate::r#gen::Init::Data::ToString::Extra::{
    l_List_toString___redArg, l_instToStringArray___redArg___lam__0,
};
use crate::r#gen::Init::Prelude::l_Nat_decEq___boxed;
use crate::r#gen::Std::Sat::CNF::{initialize_Std_Sat_CNF, runtime_initialize_Std_Sat_CNF};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_5, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1_value:
    LeanStringObject<41> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76,
        82, 65, 84, 46, 65, 99, 116, 105, 111, 110, 46, 97, 100, 100, 69, 109, 112, 116, 121, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76,
        82, 65, 84, 46, 65, 99, 116, 105, 111, 110, 46, 97, 100, 100, 82, 117, 112, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instRepr___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Bool_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprTupleOfRepr___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprTupleOfRepr___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13_value:
    LeanClosureObject<4> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Prod_repr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76,
        82, 65, 84, 46, 65, 99, 116, 105, 111, 110, 46, 97, 100, 100, 82, 97, 116, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17_value:
    LeanStringObject<36> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76,
        82, 65, 84, 46, 65, 99, 116, 105, 111, 110, 46, 100, 101, 108, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_reprFast as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1_value: LeanStringObject<
    15,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        97, 100, 100, 69, 109, 112, 116, 121, 32, 40, 105, 100, 58, 32, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [41, 32, 40, 104, 105, 110, 116, 115, 58, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3_value: LeanStringObject<
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
    m_data: [35, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4_value: LeanStringObject<
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
    m_data: [41, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 100, 100, 82, 117, 112, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [32, 40, 105, 100, 32, 58, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringProd___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 100, 100, 82, 97, 116, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 40, 105, 100, 58, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [41, 32, 40, 112, 105, 118, 111, 116, 58, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        41, 32, 40, 114, 117, 112, 32, 104, 105, 110, 116, 115, 58, 32, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        41, 32, 40, 114, 97, 116, 32, 104, 105, 110, 116, 115, 58, 32, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 101, 108, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(
    mut v_x_523_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_523_) {
        0 => {
            let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
            v___x_524_ = lean_unsigned_to_nat(0);
            return v___x_524_;
        }
        1 => {
            let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
            v___x_525_ = lean_unsigned_to_nat(1);
            return v___x_525_;
        }
        2 => {
            let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
            v___x_526_ = lean_unsigned_to_nat(2);
            return v___x_526_;
        }
        _ => {
            let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
            v___x_527_ = lean_unsigned_to_nat(3);
            return v___x_527_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg___boxed(
    mut v_x_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_529_: *mut LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(v_x_528_);
    lean_dec_ref(v_x_528_);
    return v_res_529_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx(
    mut v_00_u03b2_530_: *mut LeanObject,
    mut v_00_u03b1_531_: *mut LeanObject,
    mut v_x_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___x_533_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(v_x_532_);
    return v___x_533_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___boxed(
    mut v_00_u03b2_534_: *mut LeanObject,
    mut v_00_u03b1_535_: *mut LeanObject,
    mut v_x_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_537_: *mut LeanObject = core::ptr::null_mut();
    v_res_537_ =
        l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx(v_00_u03b2_534_, v_00_u03b1_535_, v_x_536_);
    lean_dec_ref(v_x_536_);
    return v_res_537_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(
    mut v_t_538_: *mut LeanObject,
    mut v_k_539_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_538_) {
        0 => {
            let mut v_id_540_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rupHints_541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
            v_id_540_ = lean_ctor_get(v_t_538_, 0);
            lean_inc(v_id_540_);
            v_rupHints_541_ = lean_ctor_get(v_t_538_, 1);
            lean_inc_ref(v_rupHints_541_);
            lean_dec_ref_known(v_t_538_, 2);
            v___x_542_ = lean_apply_2(v_k_539_, v_id_540_, v_rupHints_541_);
            return v___x_542_;
        }
        1 => {
            let mut v_id_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_544_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rupHints_545_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
            v_id_543_ = lean_ctor_get(v_t_538_, 0);
            lean_inc(v_id_543_);
            v_c_544_ = lean_ctor_get(v_t_538_, 1);
            lean_inc(v_c_544_);
            v_rupHints_545_ = lean_ctor_get(v_t_538_, 2);
            lean_inc_ref(v_rupHints_545_);
            lean_dec_ref_known(v_t_538_, 3);
            v___x_546_ = lean_apply_3(v_k_539_, v_id_543_, v_c_544_, v_rupHints_545_);
            return v___x_546_;
        }
        2 => {
            let mut v_id_547_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_548_: *mut LeanObject = core::ptr::null_mut();
            let mut v_pivot_549_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rupHints_550_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ratHints_551_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
            v_id_547_ = lean_ctor_get(v_t_538_, 0);
            lean_inc(v_id_547_);
            v_c_548_ = lean_ctor_get(v_t_538_, 1);
            lean_inc(v_c_548_);
            v_pivot_549_ = lean_ctor_get(v_t_538_, 2);
            lean_inc_ref(v_pivot_549_);
            v_rupHints_550_ = lean_ctor_get(v_t_538_, 3);
            lean_inc_ref(v_rupHints_550_);
            v_ratHints_551_ = lean_ctor_get(v_t_538_, 4);
            lean_inc_ref(v_ratHints_551_);
            lean_dec_ref_known(v_t_538_, 5);
            v___x_552_ = lean_apply_5(
                v_k_539_,
                v_id_547_,
                v_c_548_,
                v_pivot_549_,
                v_rupHints_550_,
                v_ratHints_551_,
            );
            return v___x_552_;
        }
        _ => {
            let mut v_ids_553_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            v_ids_553_ = lean_ctor_get(v_t_538_, 0);
            lean_inc_ref(v_ids_553_);
            lean_dec_ref_known(v_t_538_, 1);
            v___x_554_ = lean_apply_1(v_k_539_, v_ids_553_);
            return v___x_554_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(
    mut v_00_u03b2_555_: *mut LeanObject,
    mut v_00_u03b1_556_: *mut LeanObject,
    mut v_motive_557_: *mut LeanObject,
    mut v_ctorIdx_558_: *mut LeanObject,
    mut v_t_559_: *mut LeanObject,
    mut v_h_560_: *mut LeanObject,
    mut v_k_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    v___x_562_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_559_, v_k_561_);
    return v___x_562_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___boxed(
    mut v_00_u03b2_563_: *mut LeanObject,
    mut v_00_u03b1_564_: *mut LeanObject,
    mut v_motive_565_: *mut LeanObject,
    mut v_ctorIdx_566_: *mut LeanObject,
    mut v_t_567_: *mut LeanObject,
    mut v_h_568_: *mut LeanObject,
    mut v_k_569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_570_: *mut LeanObject = core::ptr::null_mut();
    v_res_570_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(
        v_00_u03b2_563_,
        v_00_u03b1_564_,
        v_motive_565_,
        v_ctorIdx_566_,
        v_t_567_,
        v_h_568_,
        v_k_569_,
    );
    lean_dec(v_ctorIdx_566_);
    return v_res_570_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim___redArg(
    mut v_t_571_: *mut LeanObject,
    mut v_addEmpty_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_571_, v_addEmpty_572_);
    return v___x_573_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim(
    mut v_00_u03b2_574_: *mut LeanObject,
    mut v_00_u03b1_575_: *mut LeanObject,
    mut v_motive_576_: *mut LeanObject,
    mut v_t_577_: *mut LeanObject,
    mut v_h_578_: *mut LeanObject,
    mut v_addEmpty_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    v___x_580_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_577_, v_addEmpty_579_);
    return v___x_580_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim___redArg(
    mut v_t_581_: *mut LeanObject,
    mut v_addRup_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    v___x_583_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_581_, v_addRup_582_);
    return v___x_583_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim(
    mut v_00_u03b2_584_: *mut LeanObject,
    mut v_00_u03b1_585_: *mut LeanObject,
    mut v_motive_586_: *mut LeanObject,
    mut v_t_587_: *mut LeanObject,
    mut v_h_588_: *mut LeanObject,
    mut v_addRup_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    v___x_590_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_587_, v_addRup_589_);
    return v___x_590_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim___redArg(
    mut v_t_591_: *mut LeanObject,
    mut v_addRat_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    v___x_593_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_591_, v_addRat_592_);
    return v___x_593_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim(
    mut v_00_u03b2_594_: *mut LeanObject,
    mut v_00_u03b1_595_: *mut LeanObject,
    mut v_motive_596_: *mut LeanObject,
    mut v_t_597_: *mut LeanObject,
    mut v_h_598_: *mut LeanObject,
    mut v_addRat_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_597_, v_addRat_599_);
    return v___x_600_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_del_elim___redArg(
    mut v_t_601_: *mut LeanObject,
    mut v_del_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    v___x_603_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_601_, v_del_602_);
    return v___x_603_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_del_elim(
    mut v_00_u03b2_604_: *mut LeanObject,
    mut v_00_u03b1_605_: *mut LeanObject,
    mut v_motive_606_: *mut LeanObject,
    mut v_t_607_: *mut LeanObject,
    mut v_h_608_: *mut LeanObject,
    mut v_del_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_607_, v_del_609_);
    return v___x_610_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(
    mut v_00_u03b2_616_: *mut LeanObject,
    mut v_00_u03b1_617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1;
    return v___x_618_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0() -> *mut LeanObject
{
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    v___x_619_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_box(0), lean_box(0));
    return v___x_619_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instInhabitedAction(
    mut v_a_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0_once),
        _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0,
    );
    return v___x_622_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(
    mut v___f_623_: *mut LeanObject,
    mut v_x_624_: *mut LeanObject,
    mut v_x_625_: *mut LeanObject,
) -> u8 {
    let mut v_fst_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    v_fst_626_ = lean_ctor_get(v_x_624_, 0);
    v_snd_627_ = lean_ctor_get(v_x_624_, 1);
    v_fst_628_ = lean_ctor_get(v_x_625_, 0);
    v_snd_629_ = lean_ctor_get(v_x_625_, 1);
    v___x_630_ = lean_nat_dec_eq(v_fst_626_, v_fst_628_);
    if v___x_630_ == 0 {
        lean_dec_ref(v___f_623_);
        return v___x_630_;
    } else {
        let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_633_: u8 = 0;
        v___x_631_ = lean_array_get_size(v_snd_627_);
        v___x_632_ = lean_array_get_size(v_snd_629_);
        v___x_633_ = lean_nat_dec_eq(v___x_631_, v___x_632_);
        if v___x_633_ == 0 {
            lean_dec_ref(v___f_623_);
            return v___x_633_;
        } else {
            let mut v___x_634_: u8 = 0;
            v___x_634_ = l_Array_isEqvAux___redArg(v_snd_627_, v_snd_629_, v___f_623_, v___x_631_);
            return v___x_634_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed(
    mut v___f_635_: *mut LeanObject,
    mut v_x_636_: *mut LeanObject,
    mut v_x_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_638_: u8 = 0;
    let mut v_r_639_: *mut LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(
        v___f_635_, v_x_636_, v_x_637_,
    );
    lean_dec_ref(v_x_637_);
    lean_dec_ref(v_x_636_);
    v_r_639_ = lean_box((v_res_638_) as usize);
    return v_r_639_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(
    mut v_inst_643_: *mut LeanObject,
    mut v_inst_644_: *mut LeanObject,
    mut v_x_645_: *mut LeanObject,
    mut v_x_646_: *mut LeanObject,
) -> u8 {
    let mut v_id_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v___f_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: u8 = 0;
    let mut v_id_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: u8 = 0;
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    let mut v___f_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: u8 = 0;
    let mut v_id_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: u8 = 0;
    let mut v_fst_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: u8 = 0;
    let mut v___f_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: u8 = 0;
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: u8 = 0;
    let mut v___x_706_: u8 = 0;
    let mut v___x_707_: u8 = 0;
    let mut v___x_708_: u8 = 0;
    let mut v___x_709_: u8 = 0;
    let mut v___x_710_: u8 = 0;
    let mut v___x_711_: u8 = 0;
    let mut v_ids_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: u8 = 0;
    let mut v___f_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: u8 = 0;
    let mut v___x_719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_645_) {
                0 => {
                    lean_dec_ref(v_inst_644_);
                    lean_dec_ref(v_inst_643_);
                    if lean_obj_tag(v_x_646_) == 0 {
                        v_id_647_ = lean_ctor_get(v_x_645_, 0);
                        lean_inc(v_id_647_);
                        v_rupHints_648_ = lean_ctor_get(v_x_645_, 1);
                        lean_inc_ref(v_rupHints_648_);
                        lean_dec_ref_known(v_x_645_, 2);
                        v_id_649_ = lean_ctor_get(v_x_646_, 0);
                        lean_inc(v_id_649_);
                        v_rupHints_650_ = lean_ctor_get(v_x_646_, 1);
                        lean_inc_ref(v_rupHints_650_);
                        lean_dec_ref_known(v_x_646_, 2);
                        v___x_651_ = lean_nat_dec_eq(v_id_647_, v_id_649_);
                        lean_dec(v_id_649_);
                        lean_dec(v_id_647_);
                        if v___x_651_ == 0 {
                            lean_dec_ref(v_rupHints_650_);
                            lean_dec_ref(v_rupHints_648_);
                            return v___x_651_;
                        } else {
                            v___x_652_ = lean_array_get_size(v_rupHints_648_);
                            v___x_653_ = lean_array_get_size(v_rupHints_650_);
                            v___x_654_ = lean_nat_dec_eq(v___x_652_, v___x_653_);
                            if v___x_654_ == 0 {
                                lean_dec_ref(v_rupHints_650_);
                                lean_dec_ref(v_rupHints_648_);
                                return v___x_654_;
                            } else {
                                v___f_655_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0;
                                v___x_656_ = l_Array_isEqvAux___redArg(
                                    v_rupHints_648_,
                                    v_rupHints_650_,
                                    v___f_655_,
                                    v___x_652_,
                                );
                                lean_dec_ref(v_rupHints_650_);
                                lean_dec_ref(v_rupHints_648_);
                                return v___x_656_;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_x_645_, 2);
                        lean_dec_ref(v_x_646_);
                        v___x_657_ = 0;
                        return v___x_657_;
                    }
                }
                1 => {
                    lean_dec_ref(v_inst_644_);
                    if lean_obj_tag(v_x_646_) == 1 {
                        v_id_658_ = lean_ctor_get(v_x_645_, 0);
                        lean_inc(v_id_658_);
                        v_c_659_ = lean_ctor_get(v_x_645_, 1);
                        lean_inc(v_c_659_);
                        v_rupHints_660_ = lean_ctor_get(v_x_645_, 2);
                        lean_inc_ref(v_rupHints_660_);
                        lean_dec_ref_known(v_x_645_, 3);
                        v_id_661_ = lean_ctor_get(v_x_646_, 0);
                        lean_inc(v_id_661_);
                        v_c_662_ = lean_ctor_get(v_x_646_, 1);
                        lean_inc(v_c_662_);
                        v_rupHints_663_ = lean_ctor_get(v_x_646_, 2);
                        lean_inc_ref(v_rupHints_663_);
                        lean_dec_ref_known(v_x_646_, 3);
                        v___x_664_ = lean_nat_dec_eq(v_id_658_, v_id_661_);
                        lean_dec(v_id_661_);
                        lean_dec(v_id_658_);
                        if v___x_664_ == 0 {
                            lean_dec_ref(v_rupHints_663_);
                            lean_dec(v_c_662_);
                            lean_dec_ref(v_rupHints_660_);
                            lean_dec(v_c_659_);
                            lean_dec_ref(v_inst_643_);
                            return v___x_664_;
                        } else {
                            v___x_665_ = lean_apply_2(v_inst_643_, v_c_659_, v_c_662_);
                            v___x_666_ = (lean_unbox(v___x_665_) as u8);
                            if v___x_666_ == 0 {
                                lean_dec_ref(v_rupHints_663_);
                                lean_dec_ref(v_rupHints_660_);
                                v___x_667_ = (lean_unbox(v___x_665_) as u8);
                                return v___x_667_;
                            } else {
                                v___x_668_ = lean_array_get_size(v_rupHints_660_);
                                v___x_669_ = lean_array_get_size(v_rupHints_663_);
                                v___x_670_ = lean_nat_dec_eq(v___x_668_, v___x_669_);
                                if v___x_670_ == 0 {
                                    lean_dec_ref(v_rupHints_663_);
                                    lean_dec_ref(v_rupHints_660_);
                                    return v___x_670_;
                                } else {
                                    v___f_671_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0;
                                    v___x_672_ = l_Array_isEqvAux___redArg(
                                        v_rupHints_660_,
                                        v_rupHints_663_,
                                        v___f_671_,
                                        v___x_668_,
                                    );
                                    lean_dec_ref(v_rupHints_663_);
                                    lean_dec_ref(v_rupHints_660_);
                                    return v___x_672_;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_x_645_, 3);
                        lean_dec_ref(v_x_646_);
                        lean_dec_ref(v_inst_643_);
                        v___x_673_ = 0;
                        return v___x_673_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_x_646_) == 2 {
                        v_id_674_ = lean_ctor_get(v_x_645_, 0);
                        lean_inc(v_id_674_);
                        v_c_675_ = lean_ctor_get(v_x_645_, 1);
                        lean_inc(v_c_675_);
                        v_pivot_676_ = lean_ctor_get(v_x_645_, 2);
                        lean_inc_ref(v_pivot_676_);
                        v_rupHints_677_ = lean_ctor_get(v_x_645_, 3);
                        lean_inc_ref(v_rupHints_677_);
                        v_ratHints_678_ = lean_ctor_get(v_x_645_, 4);
                        lean_inc_ref(v_ratHints_678_);
                        lean_dec_ref_known(v_x_645_, 5);
                        v_id_679_ = lean_ctor_get(v_x_646_, 0);
                        lean_inc(v_id_679_);
                        v_c_680_ = lean_ctor_get(v_x_646_, 1);
                        lean_inc(v_c_680_);
                        v_pivot_681_ = lean_ctor_get(v_x_646_, 2);
                        lean_inc_ref(v_pivot_681_);
                        v_rupHints_682_ = lean_ctor_get(v_x_646_, 3);
                        lean_inc_ref(v_rupHints_682_);
                        v_ratHints_683_ = lean_ctor_get(v_x_646_, 4);
                        lean_inc_ref(v_ratHints_683_);
                        lean_dec_ref_known(v_x_646_, 5);
                        v___x_684_ = lean_nat_dec_eq(v_id_674_, v_id_679_);
                        lean_dec(v_id_679_);
                        lean_dec(v_id_674_);
                        if v___x_684_ == 0 {
                            lean_dec_ref(v_ratHints_683_);
                            lean_dec_ref(v_rupHints_682_);
                            lean_dec_ref(v_pivot_681_);
                            lean_dec(v_c_680_);
                            lean_dec_ref(v_ratHints_678_);
                            lean_dec_ref(v_rupHints_677_);
                            lean_dec_ref(v_pivot_676_);
                            lean_dec(v_c_675_);
                            lean_dec_ref(v_inst_644_);
                            lean_dec_ref(v_inst_643_);
                            return v___x_684_;
                        } else {
                            v___x_685_ = lean_apply_2(v_inst_643_, v_c_675_, v_c_680_);
                            v___x_686_ = (lean_unbox(v___x_685_) as u8);
                            if v___x_686_ == 0 {
                                lean_dec_ref(v_ratHints_683_);
                                lean_dec_ref(v_rupHints_682_);
                                lean_dec_ref(v_pivot_681_);
                                lean_dec_ref(v_ratHints_678_);
                                lean_dec_ref(v_rupHints_677_);
                                lean_dec_ref(v_pivot_676_);
                                lean_dec_ref(v_inst_644_);
                                v___x_687_ = (lean_unbox(v___x_685_) as u8);
                                return v___x_687_;
                            } else {
                                v_fst_688_ = lean_ctor_get(v_pivot_676_, 0);
                                lean_inc(v_fst_688_);
                                v_snd_689_ = lean_ctor_get(v_pivot_676_, 1);
                                lean_inc(v_snd_689_);
                                lean_dec_ref(v_pivot_676_);
                                v_fst_690_ = lean_ctor_get(v_pivot_681_, 0);
                                lean_inc(v_fst_690_);
                                v_snd_691_ = lean_ctor_get(v_pivot_681_, 1);
                                lean_inc(v_snd_691_);
                                lean_dec_ref(v_pivot_681_);
                                v___x_692_ = lean_apply_2(v_inst_644_, v_fst_688_, v_fst_690_);
                                v___x_693_ = (lean_unbox(v___x_692_) as u8);
                                if v___x_693_ == 0 {
                                    lean_dec(v_snd_691_);
                                    lean_dec(v_snd_689_);
                                    lean_dec_ref(v_ratHints_683_);
                                    lean_dec_ref(v_rupHints_682_);
                                    lean_dec_ref(v_ratHints_678_);
                                    lean_dec_ref(v_rupHints_677_);
                                    v___x_694_ = (lean_unbox(v___x_692_) as u8);
                                    return v___x_694_;
                                } else {
                                    v___f_695_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0;
                                    v___f_696_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1;
                                    v___x_706_ = (lean_unbox(v_snd_689_) as u8);
                                    if v___x_706_ == 0 {
                                        v___x_707_ = (lean_unbox(v_snd_691_) as u8);
                                        lean_dec(v_snd_691_);
                                        if v___x_707_ == 0 {
                                            lean_dec(v_snd_689_);
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_ratHints_683_);
                                            lean_dec_ref(v_rupHints_682_);
                                            lean_dec_ref(v_ratHints_678_);
                                            lean_dec_ref(v_rupHints_677_);
                                            v___x_708_ = (lean_unbox(v_snd_689_) as u8);
                                            lean_dec(v_snd_689_);
                                            return v___x_708_;
                                        }
                                    } else {
                                        lean_dec(v_snd_689_);
                                        v___x_709_ = (lean_unbox(v_snd_691_) as u8);
                                        if v___x_709_ == 0 {
                                            lean_dec_ref(v_ratHints_683_);
                                            lean_dec_ref(v_rupHints_682_);
                                            lean_dec_ref(v_ratHints_678_);
                                            lean_dec_ref(v_rupHints_677_);
                                            v___x_710_ = (lean_unbox(v_snd_691_) as u8);
                                            lean_dec(v_snd_691_);
                                            return v___x_710_;
                                        } else {
                                            lean_dec(v_snd_691_);
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_x_645_, 5);
                        lean_dec_ref(v_x_646_);
                        lean_dec_ref(v_inst_644_);
                        lean_dec_ref(v_inst_643_);
                        v___x_711_ = 0;
                        return v___x_711_;
                    }
                }
                _ => {
                    lean_dec_ref(v_inst_644_);
                    lean_dec_ref(v_inst_643_);
                    if lean_obj_tag(v_x_646_) == 3 {
                        v_ids_712_ = lean_ctor_get(v_x_645_, 0);
                        lean_inc_ref(v_ids_712_);
                        lean_dec_ref_known(v_x_645_, 1);
                        v_ids_713_ = lean_ctor_get(v_x_646_, 0);
                        lean_inc_ref(v_ids_713_);
                        lean_dec_ref_known(v_x_646_, 1);
                        v___x_714_ = lean_array_get_size(v_ids_712_);
                        v___x_715_ = lean_array_get_size(v_ids_713_);
                        v___x_716_ = lean_nat_dec_eq(v___x_714_, v___x_715_);
                        if v___x_716_ == 0 {
                            lean_dec_ref(v_ids_713_);
                            lean_dec_ref(v_ids_712_);
                            return v___x_716_;
                        } else {
                            v___f_717_ =
                                l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0;
                            v___x_718_ = l_Array_isEqvAux___redArg(
                                v_ids_712_, v_ids_713_, v___f_717_, v___x_714_,
                            );
                            lean_dec_ref(v_ids_713_);
                            lean_dec_ref(v_ids_712_);
                            return v___x_718_;
                        }
                    } else {
                        lean_dec_ref_known(v_x_645_, 1);
                        lean_dec_ref(v_x_646_);
                        v___x_719_ = 0;
                        return v___x_719_;
                    }
                }
            },
            1 => {
                v___x_698_ = lean_array_get_size(v_rupHints_677_);
                v___x_699_ = lean_array_get_size(v_rupHints_682_);
                v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
                if v___x_700_ == 0 {
                    lean_dec_ref(v_ratHints_683_);
                    lean_dec_ref(v_rupHints_682_);
                    lean_dec_ref(v_ratHints_678_);
                    lean_dec_ref(v_rupHints_677_);
                    return v___x_700_;
                } else {
                    v___x_701_ = l_Array_isEqvAux___redArg(
                        v_rupHints_677_,
                        v_rupHints_682_,
                        v___f_695_,
                        v___x_698_,
                    );
                    lean_dec_ref(v_rupHints_682_);
                    lean_dec_ref(v_rupHints_677_);
                    if v___x_701_ == 0 {
                        lean_dec_ref(v_ratHints_683_);
                        lean_dec_ref(v_ratHints_678_);
                        return v___x_701_;
                    } else {
                        v___x_702_ = lean_array_get_size(v_ratHints_678_);
                        v___x_703_ = lean_array_get_size(v_ratHints_683_);
                        v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
                        if v___x_704_ == 0 {
                            lean_dec_ref(v_ratHints_683_);
                            lean_dec_ref(v_ratHints_678_);
                            return v___x_704_;
                        } else {
                            v___x_705_ = l_Array_isEqvAux___redArg(
                                v_ratHints_678_,
                                v_ratHints_683_,
                                v___f_696_,
                                v___x_702_,
                            );
                            lean_dec_ref(v_ratHints_683_);
                            lean_dec_ref(v_ratHints_678_);
                            return v___x_705_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___boxed(
    mut v_inst_720_: *mut LeanObject,
    mut v_inst_721_: *mut LeanObject,
    mut v_x_722_: *mut LeanObject,
    mut v_x_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_724_: u8 = 0;
    let mut v_r_725_: *mut LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(
        v_inst_720_,
        v_inst_721_,
        v_x_722_,
        v_x_723_,
    );
    v_r_725_ = lean_box((v_res_724_) as usize);
    return v_r_725_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(
    mut v_00_u03b2_726_: *mut LeanObject,
    mut v_00_u03b1_727_: *mut LeanObject,
    mut v_inst_728_: *mut LeanObject,
    mut v_inst_729_: *mut LeanObject,
    mut v_x_730_: *mut LeanObject,
    mut v_x_731_: *mut LeanObject,
) -> u8 {
    let mut v___x_732_: u8 = 0;
    v___x_732_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(
        v_inst_728_,
        v_inst_729_,
        v_x_730_,
        v_x_731_,
    );
    return v___x_732_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed(
    mut v_00_u03b2_733_: *mut LeanObject,
    mut v_00_u03b1_734_: *mut LeanObject,
    mut v_inst_735_: *mut LeanObject,
    mut v_inst_736_: *mut LeanObject,
    mut v_x_737_: *mut LeanObject,
    mut v_x_738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_739_: u8 = 0;
    let mut v_r_740_: *mut LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(
        v_00_u03b2_733_,
        v_00_u03b1_734_,
        v_inst_735_,
        v_inst_736_,
        v_x_737_,
        v_x_738_,
    );
    v_r_740_ = lean_box((v_res_739_) as usize);
    return v_r_740_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction___redArg(
    mut v_inst_741_: *mut LeanObject,
    mut v_inst_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_743_, 0, lean_box(0));
    lean_closure_set(v___x_743_, 1, lean_box(0));
    lean_closure_set(v___x_743_, 2, v_inst_741_);
    lean_closure_set(v___x_743_, 3, v_inst_742_);
    return v___x_743_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instBEqAction(
    mut v_00_u03b2_744_: *mut LeanObject,
    mut v_00_u03b1_745_: *mut LeanObject,
    mut v_inst_746_: *mut LeanObject,
    mut v_inst_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_748_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_748_, 0, lean_box(0));
    lean_closure_set(v___x_748_, 1, lean_box(0));
    lean_closure_set(v___x_748_, 2, v_inst_746_);
    lean_closure_set(v___x_748_, 3, v_inst_747_);
    return v___x_748_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ = lean_unsigned_to_nat(2);
    v___x_757_ = lean_nat_to_int(v___x_756_);
    return v___x_757_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_unsigned_to_nat(1);
    v___x_759_ = lean_nat_to_int(v___x_758_);
    return v___x_759_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(
    mut v_inst_788_: *mut LeanObject,
    mut v_inst_789_: *mut LeanObject,
    mut v_x_790_: *mut LeanObject,
    mut v_prec_791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_797_: u8 = 0;
    let mut v___y_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: u8 = 0;
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_818_: u8 = 0;
    let mut v_id_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u8 = 0;
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: u8 = 0;
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_792_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0;
                match lean_obj_tag(v_x_790_) {
                    0 => {
                        lean_dec_ref(v_inst_789_);
                        lean_dec_ref(v_inst_788_);
                        v_id_793_ = lean_ctor_get(v_x_790_, 0);
                        v_rupHints_794_ = lean_ctor_get(v_x_790_, 1);
                        v_isSharedCheck_818_ = (!lean_is_exclusive(v_x_790_)) as u8;
                        if v_isSharedCheck_818_ == 0 {
                            v___x_796_ = v_x_790_;
                            v_isShared_797_ = v_isSharedCheck_818_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_rupHints_794_);
                            lean_inc(v_id_793_);
                            lean_dec(v_x_790_);
                            v___x_796_ = lean_box(0);
                            v_isShared_797_ = v_isSharedCheck_818_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        lean_dec_ref(v_inst_789_);
                        v_id_819_ = lean_ctor_get(v_x_790_, 0);
                        lean_inc(v_id_819_);
                        v_c_820_ = lean_ctor_get(v_x_790_, 1);
                        lean_inc(v_c_820_);
                        v_rupHints_821_ = lean_ctor_get(v_x_790_, 2);
                        lean_inc_ref(v_rupHints_821_);
                        lean_dec_ref_known(v_x_790_, 3);
                        v___x_840_ = lean_unsigned_to_nat(1024);
                        v___x_841_ = lean_nat_dec_le(v___x_840_, v_prec_791_);
                        if v___x_841_ == 0 {
                            v___x_842_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
                            v___y_823_ = v___x_842_;
                            state = 4;
                            continue;
                        } else {
                            v___x_843_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
                            v___y_823_ = v___x_843_;
                            state = 4;
                            continue;
                        }
                    }
                    2 => {
                        v_id_844_ = lean_ctor_get(v_x_790_, 0);
                        lean_inc(v_id_844_);
                        v_c_845_ = lean_ctor_get(v_x_790_, 1);
                        lean_inc(v_c_845_);
                        v_pivot_846_ = lean_ctor_get(v_x_790_, 2);
                        lean_inc_ref(v_pivot_846_);
                        v_rupHints_847_ = lean_ctor_get(v_x_790_, 3);
                        lean_inc_ref(v_rupHints_847_);
                        v_ratHints_848_ = lean_ctor_get(v_x_790_, 4);
                        lean_inc_ref(v_ratHints_848_);
                        lean_dec_ref_known(v_x_790_, 5);
                        v___f_849_ =
                            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11;
                        v___x_850_ =
                            l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13;
                        v___x_875_ = lean_unsigned_to_nat(1024);
                        v___x_876_ = lean_nat_dec_le(v___x_875_, v_prec_791_);
                        if v___x_876_ == 0 {
                            v___x_877_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
                            v___y_852_ = v___x_877_;
                            state = 5;
                            continue;
                        } else {
                            v___x_878_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
                            v___y_852_ = v___x_878_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec_ref(v_inst_789_);
                        lean_dec_ref(v_inst_788_);
                        v_ids_879_ = lean_ctor_get(v_x_790_, 0);
                        lean_inc_ref(v_ids_879_);
                        lean_dec_ref_known(v_x_790_, 1);
                        v___x_889_ = lean_unsigned_to_nat(1024);
                        v___x_890_ = lean_nat_dec_le(v___x_889_, v_prec_791_);
                        if v___x_890_ == 0 {
                            v___x_891_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
                            v___y_881_ = v___x_891_;
                            state = 6;
                            continue;
                        } else {
                            v___x_892_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
                            v___y_881_ = v___x_892_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_814_ = lean_unsigned_to_nat(1024);
                v___x_815_ = lean_nat_dec_le(v___x_814_, v_prec_791_);
                if v___x_815_ == 0 {
                    v___x_816_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
                    v___y_799_ = v___x_816_;
                    state = 2;
                    continue;
                } else {
                    v___x_817_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
                    v___y_799_ = v___x_817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_800_ = lean_box(1);
                v___x_801_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3;
                v___x_802_ = l_Nat_reprFast(v_id_793_);
                v___x_803_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_803_, 0, v___x_802_);
                if v_isShared_797_ == 0 {
                    lean_ctor_set_tag(v___x_796_, 5);
                    lean_ctor_set(v___x_796_, 1, v___x_803_);
                    lean_ctor_set(v___x_796_, 0, v___x_801_);
                    v___x_805_ = v___x_796_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_801_);
                    lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_803_);
                    v___x_805_ = v_reuseFailAlloc_813_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_806_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_806_, 0, v___x_805_);
                lean_ctor_set(v___x_806_, 1, v___x_800_);
                v___x_807_ = l_Array_repr___redArg(v___f_792_, v_rupHints_794_);
                v___x_808_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_808_, 0, v___x_806_);
                lean_ctor_set(v___x_808_, 1, v___x_807_);
                lean_inc(v___y_799_);
                v___x_809_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_809_, 0, v___y_799_);
                lean_ctor_set(v___x_809_, 1, v___x_808_);
                v___x_810_ = 0;
                v___x_811_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_811_, 0, v___x_809_);
                lean_ctor_set_uint8(
                    v___x_811_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_810_,
                );
                v___x_812_ = l_Repr_addAppParen(v___x_811_, v_prec_791_);
                return v___x_812_;
            }
            4 => {
                v___x_824_ = lean_box(1);
                v___x_825_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8;
                v___x_826_ = l_Nat_reprFast(v_id_819_);
                v___x_827_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_827_, 0, v___x_826_);
                v___x_828_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_828_, 0, v___x_825_);
                lean_ctor_set(v___x_828_, 1, v___x_827_);
                v___x_829_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_829_, 0, v___x_828_);
                lean_ctor_set(v___x_829_, 1, v___x_824_);
                v___x_830_ = lean_unsigned_to_nat(1024);
                v___x_831_ = lean_apply_2(v_inst_788_, v_c_820_, v___x_830_);
                v___x_832_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_832_, 0, v___x_829_);
                lean_ctor_set(v___x_832_, 1, v___x_831_);
                v___x_833_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_833_, 0, v___x_832_);
                lean_ctor_set(v___x_833_, 1, v___x_824_);
                v___x_834_ = l_Array_repr___redArg(v___f_792_, v_rupHints_821_);
                v___x_835_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_835_, 0, v___x_833_);
                lean_ctor_set(v___x_835_, 1, v___x_834_);
                lean_inc(v___y_823_);
                v___x_836_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_836_, 0, v___y_823_);
                lean_ctor_set(v___x_836_, 1, v___x_835_);
                v___x_837_ = 0;
                v___x_838_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_838_, 0, v___x_836_);
                lean_ctor_set_uint8(
                    v___x_838_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_837_,
                );
                v___x_839_ = l_Repr_addAppParen(v___x_838_, v_prec_791_);
                return v___x_839_;
            }
            5 => {
                v___x_853_ = lean_box(1);
                v___x_854_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16;
                v___x_855_ = l_Nat_reprFast(v_id_844_);
                v___x_856_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_856_, 0, v___x_855_);
                v___x_857_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_857_, 0, v___x_854_);
                lean_ctor_set(v___x_857_, 1, v___x_856_);
                v___x_858_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_858_, 0, v___x_857_);
                lean_ctor_set(v___x_858_, 1, v___x_853_);
                v___x_859_ = lean_unsigned_to_nat(1024);
                v___x_860_ = lean_apply_2(v_inst_788_, v_c_845_, v___x_859_);
                v___x_861_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_861_, 0, v___x_858_);
                lean_ctor_set(v___x_861_, 1, v___x_860_);
                v___x_862_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_862_, 0, v___x_861_);
                lean_ctor_set(v___x_862_, 1, v___x_853_);
                v___x_863_ = l_Prod_repr___redArg(v_inst_789_, v___f_849_, v_pivot_846_);
                v___x_864_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_864_, 0, v___x_862_);
                lean_ctor_set(v___x_864_, 1, v___x_863_);
                v___x_865_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_865_, 0, v___x_864_);
                lean_ctor_set(v___x_865_, 1, v___x_853_);
                v___x_866_ = l_Array_repr___redArg(v___f_792_, v_rupHints_847_);
                v___x_867_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_867_, 0, v___x_865_);
                lean_ctor_set(v___x_867_, 1, v___x_866_);
                v___x_868_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_868_, 0, v___x_867_);
                lean_ctor_set(v___x_868_, 1, v___x_853_);
                v___x_869_ = l_Array_repr___redArg(v___x_850_, v_ratHints_848_);
                v___x_870_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_870_, 0, v___x_868_);
                lean_ctor_set(v___x_870_, 1, v___x_869_);
                lean_inc(v___y_852_);
                v___x_871_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_871_, 0, v___y_852_);
                lean_ctor_set(v___x_871_, 1, v___x_870_);
                v___x_872_ = 0;
                v___x_873_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_873_, 0, v___x_871_);
                lean_ctor_set_uint8(
                    v___x_873_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_872_,
                );
                v___x_874_ = l_Repr_addAppParen(v___x_873_, v_prec_791_);
                return v___x_874_;
            }
            6 => {
                v___x_882_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19;
                v___x_883_ = l_Array_repr___redArg(v___f_792_, v_ids_879_);
                v___x_884_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_884_, 0, v___x_882_);
                lean_ctor_set(v___x_884_, 1, v___x_883_);
                lean_inc(v___y_881_);
                v___x_885_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_885_, 0, v___y_881_);
                lean_ctor_set(v___x_885_, 1, v___x_884_);
                v___x_886_ = 0;
                v___x_887_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_887_, 0, v___x_885_);
                lean_ctor_set_uint8(
                    v___x_887_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_886_,
                );
                v___x_888_ = l_Repr_addAppParen(v___x_887_, v_prec_791_);
                return v___x_888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___boxed(
    mut v_inst_893_: *mut LeanObject,
    mut v_inst_894_: *mut LeanObject,
    mut v_x_895_: *mut LeanObject,
    mut v_prec_896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_897_: *mut LeanObject = core::ptr::null_mut();
    v_res_897_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(
        v_inst_893_,
        v_inst_894_,
        v_x_895_,
        v_prec_896_,
    );
    lean_dec(v_prec_896_);
    return v_res_897_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(
    mut v_00_u03b2_898_: *mut LeanObject,
    mut v_00_u03b1_899_: *mut LeanObject,
    mut v_inst_900_: *mut LeanObject,
    mut v_inst_901_: *mut LeanObject,
    mut v_x_902_: *mut LeanObject,
    mut v_prec_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    v___x_904_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(
        v_inst_900_,
        v_inst_901_,
        v_x_902_,
        v_prec_903_,
    );
    return v___x_904_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed(
    mut v_00_u03b2_905_: *mut LeanObject,
    mut v_00_u03b1_906_: *mut LeanObject,
    mut v_inst_907_: *mut LeanObject,
    mut v_inst_908_: *mut LeanObject,
    mut v_x_909_: *mut LeanObject,
    mut v_prec_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_911_: *mut LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(
        v_00_u03b2_905_,
        v_00_u03b1_906_,
        v_inst_907_,
        v_inst_908_,
        v_x_909_,
        v_prec_910_,
    );
    lean_dec(v_prec_910_);
    return v_res_911_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instReprAction___redArg(
    mut v_inst_912_: *mut LeanObject,
    mut v_inst_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_914_, 0, lean_box(0));
    lean_closure_set(v___x_914_, 1, lean_box(0));
    lean_closure_set(v___x_914_, 2, v_inst_912_);
    lean_closure_set(v___x_914_, 3, v_inst_913_);
    return v___x_914_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instReprAction(
    mut v_00_u03b2_915_: *mut LeanObject,
    mut v_00_u03b1_916_: *mut LeanObject,
    mut v_inst_917_: *mut LeanObject,
    mut v_inst_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_919_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_919_, 0, lean_box(0));
    lean_closure_set(v___x_919_, 1, lean_box(0));
    lean_closure_set(v___x_919_, 2, v_inst_917_);
    lean_closure_set(v___x_919_, 3, v_inst_918_);
    return v___x_919_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(
    mut v_inst_942_: *mut LeanObject,
    mut v_inst_943_: *mut LeanObject,
    mut v_x_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_945_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0;
                match lean_obj_tag(v_x_944_) {
                    0 => {
                        lean_dec_ref(v_inst_943_);
                        lean_dec_ref(v_inst_942_);
                        v_id_946_ = lean_ctor_get(v_x_944_, 0);
                        lean_inc(v_id_946_);
                        v_rupHints_947_ = lean_ctor_get(v_x_944_, 1);
                        lean_inc_ref(v_rupHints_947_);
                        lean_dec_ref_known(v_x_944_, 2);
                        v___x_948_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1;
                        v___x_949_ = l_Nat_reprFast(v_id_946_);
                        v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
                        lean_dec_ref(v___x_949_);
                        v___x_951_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2;
                        v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
                        v___x_953_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3;
                        v___x_954_ = lean_array_to_list(v_rupHints_947_);
                        v___x_955_ = l_List_toString___redArg(v___f_945_, v___x_954_);
                        v___x_956_ = lean_string_append(v___x_953_, v___x_955_);
                        lean_dec_ref(v___x_955_);
                        v___x_957_ = lean_string_append(v___x_952_, v___x_956_);
                        lean_dec_ref(v___x_956_);
                        v___x_958_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4;
                        v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
                        return v___x_959_;
                    }
                    1 => {
                        lean_dec_ref(v_inst_943_);
                        v_id_960_ = lean_ctor_get(v_x_944_, 0);
                        lean_inc(v_id_960_);
                        v_c_961_ = lean_ctor_get(v_x_944_, 1);
                        lean_inc(v_c_961_);
                        v_rupHints_962_ = lean_ctor_get(v_x_944_, 2);
                        lean_inc_ref(v_rupHints_962_);
                        lean_dec_ref_known(v_x_944_, 3);
                        v___x_963_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5;
                        v___x_964_ = lean_apply_1(v_inst_942_, v_c_961_);
                        v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
                        lean_dec_ref(v___x_964_);
                        v___x_966_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6;
                        v___x_967_ = lean_string_append(v___x_965_, v___x_966_);
                        v___x_968_ = l_Nat_reprFast(v_id_960_);
                        v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
                        lean_dec_ref(v___x_968_);
                        v___x_970_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2;
                        v___x_971_ = lean_string_append(v___x_969_, v___x_970_);
                        v___x_972_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3;
                        v___x_973_ = lean_array_to_list(v_rupHints_962_);
                        v___x_974_ = l_List_toString___redArg(v___f_945_, v___x_973_);
                        v___x_975_ = lean_string_append(v___x_972_, v___x_974_);
                        lean_dec_ref(v___x_974_);
                        v___x_976_ = lean_string_append(v___x_971_, v___x_975_);
                        lean_dec_ref(v___x_975_);
                        v___x_977_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4;
                        v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
                        return v___x_978_;
                    }
                    2 => {
                        v_pivot_979_ = lean_ctor_get(v_x_944_, 2);
                        lean_inc_ref(v_pivot_979_);
                        v_id_980_ = lean_ctor_get(v_x_944_, 0);
                        lean_inc(v_id_980_);
                        v_c_981_ = lean_ctor_get(v_x_944_, 1);
                        lean_inc(v_c_981_);
                        v_rupHints_982_ = lean_ctor_get(v_x_944_, 3);
                        lean_inc_ref(v_rupHints_982_);
                        v_ratHints_983_ = lean_ctor_get(v_x_944_, 4);
                        lean_inc_ref(v_ratHints_983_);
                        lean_dec_ref_known(v_x_944_, 5);
                        v_fst_984_ = lean_ctor_get(v_pivot_979_, 0);
                        lean_inc(v_fst_984_);
                        v_snd_985_ = lean_ctor_get(v_pivot_979_, 1);
                        lean_inc(v_snd_985_);
                        lean_dec_ref(v_pivot_979_);
                        v___f_986_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8;
                        v___x_987_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9;
                        v___x_988_ = lean_apply_1(v_inst_942_, v_c_981_);
                        v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
                        lean_dec_ref(v___x_988_);
                        v___x_990_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10;
                        v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
                        v___x_992_ = l_Nat_reprFast(v_id_980_);
                        v___x_993_ = lean_string_append(v___x_991_, v___x_992_);
                        lean_dec_ref(v___x_992_);
                        v___x_994_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11;
                        v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
                        v___x_996_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12;
                        v___x_997_ = lean_apply_1(v_inst_943_, v_fst_984_);
                        v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
                        lean_dec_ref(v___x_997_);
                        v___x_999_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13;
                        v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
                        v___x_1021_ = (lean_unbox(v_snd_985_) as u8);
                        lean_dec(v_snd_985_);
                        if v___x_1021_ == 0 {
                            v___x_1022_ =
                                l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16;
                            v___y_1002_ = v___x_1022_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1023_ =
                                l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17;
                            v___y_1002_ = v___x_1023_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec_ref(v_inst_943_);
                        lean_dec_ref(v_inst_942_);
                        v_ids_1024_ = lean_ctor_get(v_x_944_, 0);
                        lean_inc_ref(v_ids_1024_);
                        lean_dec_ref_known(v_x_944_, 1);
                        v___x_1025_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18;
                        v___x_1026_ =
                            l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3;
                        v___x_1027_ = lean_array_to_list(v_ids_1024_);
                        v___x_1028_ = l_List_toString___redArg(v___f_945_, v___x_1027_);
                        v___x_1029_ = lean_string_append(v___x_1026_, v___x_1028_);
                        lean_dec_ref(v___x_1028_);
                        v___x_1030_ = lean_string_append(v___x_1025_, v___x_1029_);
                        lean_dec_ref(v___x_1029_);
                        return v___x_1030_;
                    }
                }
            }
            1 => {
                v___x_1003_ = lean_string_append(v___x_1000_, v___y_1002_);
                v___x_1004_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4;
                v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
                v___x_1006_ = lean_string_append(v___x_995_, v___x_1005_);
                lean_dec_ref(v___x_1005_);
                v___x_1007_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14;
                v___x_1008_ = lean_string_append(v___x_1006_, v___x_1007_);
                v___x_1009_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3;
                v___x_1010_ = lean_array_to_list(v_rupHints_982_);
                v___x_1011_ = l_List_toString___redArg(v___f_945_, v___x_1010_);
                v___x_1012_ = lean_string_append(v___x_1009_, v___x_1011_);
                lean_dec_ref(v___x_1011_);
                v___x_1013_ = lean_string_append(v___x_1008_, v___x_1012_);
                lean_dec_ref(v___x_1012_);
                v___x_1014_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15;
                v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
                v___x_1016_ = lean_array_to_list(v_ratHints_983_);
                v___x_1017_ = l_List_toString___redArg(v___f_986_, v___x_1016_);
                v___x_1018_ = lean_string_append(v___x_1009_, v___x_1017_);
                lean_dec_ref(v___x_1017_);
                v___x_1019_ = lean_string_append(v___x_1015_, v___x_1018_);
                lean_dec_ref(v___x_1018_);
                v___x_1020_ = lean_string_append(v___x_1019_, v___x_1004_);
                return v___x_1020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Action_toString(
    mut v_00_u03b2_1031_: *mut LeanObject,
    mut v_00_u03b1_1032_: *mut LeanObject,
    mut v_inst_1033_: *mut LeanObject,
    mut v_inst_1034_: *mut LeanObject,
    mut v_x_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    v___x_1036_ =
        l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(v_inst_1033_, v_inst_1034_, v_x_1035_);
    return v___x_1036_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instToStringAction___redArg(
    mut v_inst_1037_: *mut LeanObject,
    mut v_inst_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    v___x_1039_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Action_toString as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1039_, 0, lean_box(0));
    lean_closure_set(v___x_1039_, 1, lean_box(0));
    lean_closure_set(v___x_1039_, 2, v_inst_1037_);
    lean_closure_set(v___x_1039_, 3, v_inst_1038_);
    return v___x_1039_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_instToStringAction(
    mut v_00_u03b2_1040_: *mut LeanObject,
    mut v_00_u03b1_1041_: *mut LeanObject,
    mut v_inst_1042_: *mut LeanObject,
    mut v_inst_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    v___x_1044_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Action_toString as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1044_, 0, lean_box(0));
    lean_closure_set(v___x_1044_, 1, lean_box(0));
    lean_closure_set(v___x_1044_, 2, v_inst_1042_);
    lean_closure_set(v___x_1044_, 3, v_inst_1043_);
    return v___x_1044_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
}
