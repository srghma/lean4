// Lean compiler output
// Module: Init.GrindInstances.Ring.Nat
// Imports: Init.Grind.Ordered.Ring Init.Data.Nat.Lemmas Init.Omega
use crate::r#gen::Init::Data::Cast::l_instNatCastNat___lam__0___boxed;
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Grind::Ordered::Ring::{
    initialize_Init_Grind_Ordered_Ring, runtime_initialize_Init_Grind_Ordered_Ring,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Nat_add___boxed, l_Nat_mul___boxed, l_Nat_pow___boxed, l_instHAdd___redArg___lam__0,
    l_instOfNatNat___boxed, l_instPowNat___redArg___lam__0, l_instSMulOfMul___redArg___lam__0,
};
pub static l_Lean_Grind_instCommSemiringNat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instNatCastNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__3_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instSMulOfMul___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__5_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instPowNat___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__6_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__7_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instOfNatNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instCommSemiringNat___closed__8_value: leanh::LeanCtorObject<6> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommSemiringNat___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__8_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Grind_instCommSemiringNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommSemiringNat___closed__8_value)
        as *mut leanh::LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_Nat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_Nat(
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
pub unsafe fn initialize_Init_GrindInstances_Ring_Nat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_Nat(builtin);
}