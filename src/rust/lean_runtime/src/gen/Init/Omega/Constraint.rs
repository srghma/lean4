// Lean compiler output
// Module: Init.Omega.Constraint
// Imports: Init.Omega.Coeffs Init.Data.Int.Lemmas Init.Data.Int.Order Init.Data.ToString.Macro Init.Omega.Int Init.PropLemmas Init.RCases
use crate::r#gen::Init::Data::Int::Basic::{l_Int_instDecidableEq___boxed, l_Int_neg___boxed};
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_bmod;
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Option::Basic::{
    l_Option_instDecidableEq___redArg, l_Option_merge___redArg,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::String::Bootstrap::l_String_Internal_append___boxed;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Omega::Coeffs::{
    initialize_Init_Omega_Coeffs, runtime_initialize_Init_Omega_Coeffs,
};
use crate::r#gen::Init::Omega::Int::{
    initialize_Init_Omega_Int, runtime_initialize_Init_Omega_Int,
};
use crate::r#gen::Init::Omega::IntList::{
    l_Lean_Omega_IntList_dot, l_Lean_Omega_IntList_gcd, l_Lean_Omega_IntList_leading,
    l_Lean_Omega_IntList_sdiv, l_Lean_Omega_IntList_set, l_Lean_Omega_IntList_smul,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_ediv;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_length,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0_value:
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
    m_fun: l_String_Internal_append___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0_value
)
    as *mut LeanObject;
static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1_value
) as *mut LeanObject;
pub static l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0_value:
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
    m_fun: l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0_value:
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
    m_fun: l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Omega_instBEqConstraint___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_instBEqConstraint_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_instBEqConstraint___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instBEqConstraint___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_instBEqConstraint: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instBEqConstraint___closed__0_value) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1_value:
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
        l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3_value:
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
        l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__1_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [108, 111, 119, 101, 114, 66, 111, 117, 110, 100, 0],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            l_Lean_Omega_instReprConstraint_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            l_Lean_Omega_instReprConstraint_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__8_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            l_Lean_Omega_instReprConstraint_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__10_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [117, 112, 112, 101, 114, 66, 111, 117, 110, 100, 0],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            l_Lean_Omega_instReprConstraint_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__12_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__15_value: LeanCtorObject<1> =
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
            l_Lean_Omega_instReprConstraint_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint_repr___redArg___closed__16_value: LeanCtorObject<1> =
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
            l_Lean_Omega_instReprConstraint_repr___redArg___closed__12_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Omega_instReprConstraint_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Omega_instReprConstraint___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_instReprConstraint_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_instReprConstraint___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_instReprConstraint: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprConstraint___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__0_value: LeanStringObject<
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
    m_data: [93, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__1_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 7,
    m_data: [40, 45, 226, 136, 158, 44, 32, 226, 136, 158, 41, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__2_value: LeanStringObject<
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
    m_length: 5,
    m_data: [40, 45, 226, 136, 158, 44, 32, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__3_value: LeanStringObject<
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
    m_data: [91, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__4_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [44, 32, 226, 136, 158, 41, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__5_value: LeanStringObject<
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
    m_data: [44, 32, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__6_value: LeanStringObject<
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
    m_data: [123, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__7_value: LeanStringObject<
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
    m_data: [125, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___private__1___closed__8_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 136, 133, 0],
};
static mut l_Lean_Omega_Constraint_instToString___private__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___private__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Omega_Constraint_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_Constraint_instToString___private__1___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_Constraint_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_Constraint_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_Constraint_neg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_Constraint_neg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_neg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_Constraint_trivial___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Lean_Omega_Constraint_trivial___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_trivial___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_Constraint_trivial: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_trivial___closed__0_value) as *mut LeanObject;
static mut l_Lean_Omega_Constraint_impossible___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_Constraint_impossible___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Omega_Constraint_impossible___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_Constraint_impossible___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Omega_Constraint_impossible___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_Constraint_impossible___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Omega_Constraint_impossible___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_Constraint_impossible___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Omega_Constraint_impossible: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Omega_Constraint_scale___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_Constraint_scale___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Omega_Constraint_combine___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_Constraint_combine___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_Constraint_combine___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_combine___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_Constraint_combine___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_Constraint_combine___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_Constraint_combine___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_Constraint_combine___closed__1_value) as *mut LeanObject;
static mut l_Lean_Omega_positivize_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_positivize_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Omega_LowerBound_sat(
    mut v_b_820_: *mut LeanObject,
    mut v_t_821_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_b_820_) == 0 {
        let mut v___x_822_: u8 = 0;
        v___x_822_ = 1;
        return v___x_822_;
    } else {
        let mut v_val_823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_824_: u8 = 0;
        v_val_823_ = lean_ctor_get(v_b_820_, 0);
        v___x_824_ = lean_int_dec_le(v_val_823_, v_t_821_);
        return v___x_824_;
    }
}
pub unsafe fn l_Lean_Omega_LowerBound_sat___boxed(
    mut v_b_825_: *mut LeanObject,
    mut v_t_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_827_: u8 = 0;
    let mut v_r_828_: *mut LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Lean_Omega_LowerBound_sat(v_b_825_, v_t_826_);
    lean_dec(v_t_826_);
    lean_dec(v_b_825_);
    v_r_828_ = lean_box((v_res_827_) as usize);
    return v_r_828_;
}
pub unsafe fn l_Lean_Omega_UpperBound_sat(
    mut v_b_829_: *mut LeanObject,
    mut v_t_830_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_b_829_) == 0 {
        let mut v___x_831_: u8 = 0;
        v___x_831_ = 1;
        return v___x_831_;
    } else {
        let mut v_val_832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_833_: u8 = 0;
        v_val_832_ = lean_ctor_get(v_b_829_, 0);
        v___x_833_ = lean_int_dec_le(v_t_830_, v_val_832_);
        return v___x_833_;
    }
}
pub unsafe fn l_Lean_Omega_UpperBound_sat___boxed(
    mut v_b_834_: *mut LeanObject,
    mut v_t_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_836_: u8 = 0;
    let mut v_r_837_: *mut LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Lean_Omega_UpperBound_sat(v_b_834_, v_t_835_);
    lean_dec(v_t_835_);
    lean_dec(v_b_834_);
    v_r_837_ = lean_box((v_res_836_) as usize);
    return v_r_837_;
}
pub unsafe fn _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0()
-> *mut LeanObject {
    let mut v_natZero_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_841_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_840_ = lean_unsigned_to_nat(0);
    v_intZero_841_ = lean_nat_to_int(v_natZero_840_);
    return v_intZero_841_;
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(
    mut v_x_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_845_: u8 = 0;
    v_intZero_844_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
    v_isNeg_845_ = lean_int_dec_lt(v_x_843_, v_intZero_844_);
    if v_isNeg_845_ == 0 {
        let mut v_a_846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
        v_a_846_ = lean_nat_abs(v_x_843_);
        v___x_847_ = l_Nat_reprFast(v_a_846_);
        return v___x_847_;
    } else {
        let mut v_abs_848_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_849_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
        v_abs_848_ = lean_nat_abs(v_x_843_);
        v_one_849_ = lean_unsigned_to_nat(1);
        v_a_850_ = lean_nat_sub(v_abs_848_, v_one_849_);
        lean_dec(v_abs_848_);
        v___x_851_ =
            l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
        v___x_852_ = lean_nat_add(v_a_850_, v_one_849_);
        lean_dec(v_a_850_);
        v___x_853_ = l_Nat_reprFast(v___x_852_);
        v___x_854_ = lean_string_append(v___x_851_, v___x_853_);
        lean_dec_ref(v___x_853_);
        return v___x_854_;
    }
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___boxed(
    mut v_x_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_856_: *mut LeanObject = core::ptr::null_mut();
    v_res_856_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(v_x_855_);
    lean_dec(v_x_855_);
    return v_res_856_;
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(
    mut v_i_859_: *mut LeanObject,
    mut v_prec_860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: u8 = 0;
    let mut v_a_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_865_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_866_ = lean_int_dec_lt(v_i_859_, v___x_865_);
                if v___x_866_ == 0 {
                    if v___x_866_ == 0 {
                        v_a_867_ = lean_nat_abs(v_i_859_);
                        v___x_868_ = l_Nat_reprFast(v_a_867_);
                        v___x_869_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_869_, 0, v___x_868_);
                        return v___x_869_;
                    } else {
                        v_abs_870_ = lean_nat_abs(v_i_859_);
                        v_one_871_ = lean_unsigned_to_nat(1);
                        v_a_872_ = lean_nat_sub(v_abs_870_, v_one_871_);
                        lean_dec(v_abs_870_);
                        v___x_873_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_874_ = lean_nat_add(v_a_872_, v_one_871_);
                        lean_dec(v_a_872_);
                        v___x_875_ = l_Nat_reprFast(v___x_874_);
                        v___x_876_ = lean_string_append(v___x_873_, v___x_875_);
                        lean_dec_ref(v___x_875_);
                        v___x_877_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_877_, 0, v___x_876_);
                        return v___x_877_;
                    }
                } else {
                    if v___x_866_ == 0 {
                        v_a_878_ = lean_nat_abs(v_i_859_);
                        v___x_879_ = l_Nat_reprFast(v_a_878_);
                        v___y_862_ = v___x_879_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_880_ = lean_nat_abs(v_i_859_);
                        v_one_881_ = lean_unsigned_to_nat(1);
                        v_a_882_ = lean_nat_sub(v_abs_880_, v_one_881_);
                        lean_dec(v_abs_880_);
                        v___x_883_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_884_ = lean_nat_add(v_a_882_, v_one_881_);
                        lean_dec(v_a_882_);
                        v___x_885_ = l_Nat_reprFast(v___x_884_);
                        v___x_886_ = lean_string_append(v___x_883_, v___x_885_);
                        lean_dec_ref(v___x_885_);
                        v___y_862_ = v___x_886_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_863_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_863_, 0, v___y_862_);
                v___x_864_ = l_Repr_addAppParen(v___x_863_, v_prec_860_);
                return v___x_864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0___boxed(
    mut v_i_887_: *mut LeanObject,
    mut v_prec_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_889_ =
        l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(v_i_887_, v_prec_888_);
    lean_dec(v_prec_888_);
    lean_dec(v_i_887_);
    return v_res_889_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(
    mut v_x_892_: *mut LeanObject,
    mut v_x_893_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_892_) == 0 {
        if lean_obj_tag(v_x_893_) == 0 {
            let mut v___x_894_: u8 = 0;
            v___x_894_ = 1;
            return v___x_894_;
        } else {
            let mut v___x_895_: u8 = 0;
            v___x_895_ = 0;
            return v___x_895_;
        }
    } else {
        if lean_obj_tag(v_x_893_) == 0 {
            let mut v___x_896_: u8 = 0;
            v___x_896_ = 0;
            return v___x_896_;
        } else {
            let mut v_val_897_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_898_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_899_: u8 = 0;
            v_val_897_ = lean_ctor_get(v_x_892_, 0);
            v_val_898_ = lean_ctor_get(v_x_893_, 0);
            v___x_899_ = lean_int_dec_eq(v_val_897_, v_val_898_);
            return v___x_899_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(
    mut v_x_900_: *mut LeanObject,
    mut v_x_901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_902_: u8 = 0;
    let mut v_r_903_: *mut LeanObject = core::ptr::null_mut();
    v_res_902_ =
        l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_x_900_, v_x_901_);
    lean_dec(v_x_901_);
    lean_dec(v_x_900_);
    v_r_903_ = lean_box((v_res_902_) as usize);
    return v_r_903_;
}
pub unsafe fn l_Lean_Omega_instBEqConstraint_beq(
    mut v_x_904_: *mut LeanObject,
    mut v_x_905_: *mut LeanObject,
) -> u8 {
    let mut v_lowerBound_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowerBound_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: u8 = 0;
    v_lowerBound_906_ = lean_ctor_get(v_x_904_, 0);
    v_upperBound_907_ = lean_ctor_get(v_x_904_, 1);
    v_lowerBound_908_ = lean_ctor_get(v_x_905_, 0);
    v_upperBound_909_ = lean_ctor_get(v_x_905_, 1);
    v___x_910_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(
        v_lowerBound_906_,
        v_lowerBound_908_,
    );
    if v___x_910_ == 0 {
        return v___x_910_;
    } else {
        let mut v___x_911_: u8 = 0;
        v___x_911_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(
            v_upperBound_907_,
            v_upperBound_909_,
        );
        return v___x_911_;
    }
}
pub unsafe fn l_Lean_Omega_instBEqConstraint_beq___boxed(
    mut v_x_912_: *mut LeanObject,
    mut v_x_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_914_: u8 = 0;
    let mut v_r_915_: *mut LeanObject = core::ptr::null_mut();
    v_res_914_ = l_Lean_Omega_instBEqConstraint_beq(v_x_912_, v_x_913_);
    lean_dec_ref(v_x_913_);
    lean_dec_ref(v_x_912_);
    v_r_915_ = lean_box((v_res_914_) as usize);
    return v_r_915_;
}
pub unsafe fn l_Lean_Omega_instDecidableEqConstraint_decEq(
    mut v_x_918_: *mut LeanObject,
    mut v_x_919_: *mut LeanObject,
) -> u8 {
    let mut v_lowerBound_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowerBound_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    v_lowerBound_920_ = lean_ctor_get(v_x_918_, 0);
    lean_inc(v_lowerBound_920_);
    v_upperBound_921_ = lean_ctor_get(v_x_918_, 1);
    lean_inc(v_upperBound_921_);
    lean_dec_ref(v_x_918_);
    v_lowerBound_922_ = lean_ctor_get(v_x_919_, 0);
    lean_inc(v_lowerBound_922_);
    v_upperBound_923_ = lean_ctor_get(v_x_919_, 1);
    lean_inc(v_upperBound_923_);
    lean_dec_ref(v_x_919_);
    v___x_924_ = lean_alloc_closure(
        l_Int_instDecidableEq___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    lean_inc_ref(v___x_924_);
    v___x_925_ =
        l_Option_instDecidableEq___redArg(v___x_924_, v_lowerBound_920_, v_lowerBound_922_);
    if v___x_925_ == 0 {
        lean_dec_ref(v___x_924_);
        lean_dec(v_upperBound_923_);
        lean_dec(v_upperBound_921_);
        return v___x_925_;
    } else {
        let mut v___x_926_: u8 = 0;
        v___x_926_ =
            l_Option_instDecidableEq___redArg(v___x_924_, v_upperBound_921_, v_upperBound_923_);
        return v___x_926_;
    }
}
pub unsafe fn l_Lean_Omega_instDecidableEqConstraint_decEq___boxed(
    mut v_x_927_: *mut LeanObject,
    mut v_x_928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_929_: u8 = 0;
    let mut v_r_930_: *mut LeanObject = core::ptr::null_mut();
    v_res_929_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_927_, v_x_928_);
    v_r_930_ = lean_box((v_res_929_) as usize);
    return v_r_930_;
}
pub unsafe fn l_Lean_Omega_instDecidableEqConstraint(
    mut v_x_931_: *mut LeanObject,
    mut v_x_932_: *mut LeanObject,
) -> u8 {
    let mut v___x_933_: u8 = 0;
    v___x_933_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_931_, v_x_932_);
    return v___x_933_;
}
pub unsafe fn l_Lean_Omega_instDecidableEqConstraint___boxed(
    mut v_x_934_: *mut LeanObject,
    mut v_x_935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_936_: u8 = 0;
    let mut v_r_937_: *mut LeanObject = core::ptr::null_mut();
    v_res_936_ = l_Lean_Omega_instDecidableEqConstraint(v_x_934_, v_x_935_);
    v_r_937_ = lean_box((v_res_936_) as usize);
    return v_r_937_;
}
pub unsafe fn l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(
    mut v_x_944_: *mut LeanObject,
    mut v_x_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_950_: u8 = 0;
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    let mut v_a_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_944_) == 0 {
                    v___x_946_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1;
                    return v___x_946_;
                } else {
                    v_val_947_ = lean_ctor_get(v_x_944_, 0);
                    v_isSharedCheck_989_ = (!lean_is_exclusive(v_x_944_)) as u8;
                    if v_isSharedCheck_989_ == 0 {
                        v___x_949_ = v_x_944_;
                        v_isShared_950_ = v_isSharedCheck_989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_947_);
                        lean_dec(v_x_944_);
                        v___x_949_ = lean_box(0);
                        v_isShared_950_ = v_isSharedCheck_989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_951_ =
                    l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3;
                v___x_956_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_957_ = lean_int_dec_lt(v_val_947_, v___x_956_);
                if v___x_957_ == 0 {
                    if v___x_957_ == 0 {
                        v_a_958_ = lean_nat_abs(v_val_947_);
                        lean_dec(v_val_947_);
                        v___x_959_ = l_Nat_reprFast(v_a_958_);
                        if v_isShared_950_ == 0 {
                            lean_ctor_set_tag(v___x_949_, 3);
                            lean_ctor_set(v___x_949_, 0, v___x_959_);
                            v___x_961_ = v___x_949_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_962_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
                            v___x_961_ = v_reuseFailAlloc_962_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_abs_963_ = lean_nat_abs(v_val_947_);
                        lean_dec(v_val_947_);
                        v_one_964_ = lean_unsigned_to_nat(1);
                        v_a_965_ = lean_nat_sub(v_abs_963_, v_one_964_);
                        lean_dec(v_abs_963_);
                        v___x_966_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_967_ = lean_nat_add(v_a_965_, v_one_964_);
                        lean_dec(v_a_965_);
                        v___x_968_ = l_Nat_reprFast(v___x_967_);
                        v___x_969_ = lean_string_append(v___x_966_, v___x_968_);
                        lean_dec_ref(v___x_968_);
                        if v_isShared_950_ == 0 {
                            lean_ctor_set_tag(v___x_949_, 3);
                            lean_ctor_set(v___x_949_, 0, v___x_969_);
                            v___x_971_ = v___x_949_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_972_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
                            v___x_971_ = v_reuseFailAlloc_972_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_973_ = lean_unsigned_to_nat(1024);
                    if v___x_957_ == 0 {
                        v_a_980_ = lean_nat_abs(v_val_947_);
                        lean_dec(v_val_947_);
                        v___x_981_ = l_Nat_reprFast(v_a_980_);
                        v___y_975_ = v___x_981_;
                        state = 5;
                        continue;
                    } else {
                        v_abs_982_ = lean_nat_abs(v_val_947_);
                        lean_dec(v_val_947_);
                        v_one_983_ = lean_unsigned_to_nat(1);
                        v_a_984_ = lean_nat_sub(v_abs_982_, v_one_983_);
                        lean_dec(v_abs_982_);
                        v___x_985_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_986_ = lean_nat_add(v_a_984_, v_one_983_);
                        lean_dec(v_a_984_);
                        v___x_987_ = l_Nat_reprFast(v___x_986_);
                        v___x_988_ = lean_string_append(v___x_985_, v___x_987_);
                        lean_dec_ref(v___x_987_);
                        v___y_975_ = v___x_988_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_954_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_954_, 0, v___x_951_);
                lean_ctor_set(v___x_954_, 1, v___y_953_);
                v___x_955_ = l_Repr_addAppParen(v___x_954_, v_x_945_);
                return v___x_955_;
            }
            3 => {
                v___y_953_ = v___x_961_;
                state = 2;
                continue;
            }
            4 => {
                v___y_953_ = v___x_971_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_950_ == 0 {
                    lean_ctor_set_tag(v___x_949_, 3);
                    lean_ctor_set(v___x_949_, 0, v___y_975_);
                    v___x_977_ = v___x_949_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_979_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_979_, 0, v___y_975_);
                    v___x_977_ = v_reuseFailAlloc_979_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_978_ = l_Repr_addAppParen(v___x_977_, v___x_973_);
                v___y_953_ = v___x_978_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___boxed(
    mut v_x_990_: *mut LeanObject,
    mut v_x_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_992_: *mut LeanObject = core::ptr::null_mut();
    v_res_992_ =
        l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_x_990_, v_x_991_);
    lean_dec(v_x_991_);
    return v_res_992_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Omega_instReprConstraint_repr_spec__1(
    mut v_a_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    v___x_994_ = lean_nat_to_int(v_a_993_);
    return v___x_994_;
}
pub unsafe fn _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1008_ = lean_unsigned_to_nat(14);
    v___x_1009_ = lean_nat_to_int(v___x_1008_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13() -> *mut LeanObject
{
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__0;
    v___x_1018_ = lean_string_length(v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14() -> *mut LeanObject
{
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    v___x_1019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Omega_instReprConstraint_repr___redArg___closed__13_once),
        _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13,
    );
    v___x_1020_ = lean_nat_to_int(v___x_1019_);
    return v___x_1020_;
}
pub unsafe fn l_Lean_Omega_instReprConstraint_repr___redArg(
    mut v_x_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1026_ = lean_ctor_get(v_x_1025_, 0);
                v_upperBound_1027_ = lean_ctor_get(v_x_1025_, 1);
                v_isSharedCheck_1060_ = (!lean_is_exclusive(v_x_1025_)) as u8;
                if v_isSharedCheck_1060_ == 0 {
                    v___x_1029_ = v_x_1025_;
                    v_isShared_1030_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upperBound_1027_);
                    lean_inc(v_lowerBound_1026_);
                    lean_dec(v_x_1025_);
                    v___x_1029_ = lean_box(0);
                    v_isShared_1030_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1031_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__5;
                v___x_1032_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__6;
                v___x_1033_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprConstraint_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprConstraint_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7,
                );
                v___x_1034_ = lean_unsigned_to_nat(0);
                v___x_1035_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(
                    v_lowerBound_1026_,
                    v___x_1034_,
                );
                if v_isShared_1030_ == 0 {
                    lean_ctor_set_tag(v___x_1029_, 4);
                    lean_ctor_set(v___x_1029_, 1, v___x_1035_);
                    lean_ctor_set(v___x_1029_, 0, v___x_1033_);
                    v___x_1037_ = v___x_1029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1033_);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1035_);
                    v___x_1037_ = v_reuseFailAlloc_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1038_ = 0;
                v___x_1039_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1039_, 0, v___x_1037_);
                lean_ctor_set_uint8(
                    v___x_1039_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1038_,
                );
                v___x_1040_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1040_, 0, v___x_1032_);
                lean_ctor_set(v___x_1040_, 1, v___x_1039_);
                v___x_1041_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__9;
                v___x_1042_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1042_, 0, v___x_1040_);
                lean_ctor_set(v___x_1042_, 1, v___x_1041_);
                v___x_1043_ = lean_box(1);
                v___x_1044_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1044_, 0, v___x_1042_);
                lean_ctor_set(v___x_1044_, 1, v___x_1043_);
                v___x_1045_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__11;
                v___x_1046_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1046_, 0, v___x_1044_);
                lean_ctor_set(v___x_1046_, 1, v___x_1045_);
                v___x_1047_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1047_, 0, v___x_1046_);
                lean_ctor_set(v___x_1047_, 1, v___x_1031_);
                v___x_1048_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(
                    v_upperBound_1027_,
                    v___x_1034_,
                );
                v___x_1049_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1049_, 0, v___x_1033_);
                lean_ctor_set(v___x_1049_, 1, v___x_1048_);
                v___x_1050_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1050_, 0, v___x_1049_);
                lean_ctor_set_uint8(
                    v___x_1050_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1038_,
                );
                v___x_1051_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1051_, 0, v___x_1047_);
                lean_ctor_set(v___x_1051_, 1, v___x_1050_);
                v___x_1052_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprConstraint_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprConstraint_repr___redArg___closed__14_once
                    ),
                    _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14,
                );
                v___x_1053_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__15;
                v___x_1054_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1054_, 0, v___x_1053_);
                lean_ctor_set(v___x_1054_, 1, v___x_1051_);
                v___x_1055_ = l_Lean_Omega_instReprConstraint_repr___redArg___closed__16;
                v___x_1056_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1056_, 0, v___x_1054_);
                lean_ctor_set(v___x_1056_, 1, v___x_1055_);
                v___x_1057_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1057_, 0, v___x_1052_);
                lean_ctor_set(v___x_1057_, 1, v___x_1056_);
                v___x_1058_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1058_, 0, v___x_1057_);
                lean_ctor_set_uint8(
                    v___x_1058_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1038_,
                );
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_instReprConstraint_repr(
    mut v_x_1061_: *mut LeanObject,
    mut v_prec_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    v___x_1063_ = l_Lean_Omega_instReprConstraint_repr___redArg(v_x_1061_);
    return v___x_1063_;
}
pub unsafe fn l_Lean_Omega_instReprConstraint_repr___boxed(
    mut v_x_1064_: *mut LeanObject,
    mut v_prec_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_Omega_instReprConstraint_repr(v_x_1064_, v_prec_1065_);
    lean_dec(v_prec_1065_);
    return v_res_1066_;
}
pub unsafe fn l_Lean_Omega_Constraint_instToString___private__1(
    mut v_x_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowerBound_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1096_: u8 = 0;
    let mut v_a_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1115_: u8 = 0;
    let mut v_a_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: u8 = 0;
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1136_: u8 = 0;
    let mut v_a_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1147_: u8 = 0;
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1164_: u8 = 0;
    let mut v_a_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1085_ = lean_ctor_get(v_x_1078_, 0);
                if lean_obj_tag(v_lowerBound_1085_) == 0 {
                    v_upperBound_1086_ = lean_ctor_get(v_x_1078_, 1);
                    if lean_obj_tag(v_upperBound_1086_) == 0 {
                        v___x_1087_ = l_Lean_Omega_Constraint_instToString___private__1___closed__1;
                        return v___x_1087_;
                    } else {
                        v_val_1088_ = lean_ctor_get(v_upperBound_1086_, 0);
                        v___x_1089_ = l_Lean_Omega_Constraint_instToString___private__1___closed__2;
                        v_intZero_1095_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                        v_isNeg_1096_ = lean_int_dec_lt(v_val_1088_, v_intZero_1095_);
                        if v_isNeg_1096_ == 0 {
                            v_a_1097_ = lean_nat_abs(v_val_1088_);
                            v___x_1098_ = l_Nat_reprFast(v_a_1097_);
                            v___y_1091_ = v___x_1098_;
                            state = 2;
                            continue;
                        } else {
                            v_abs_1099_ = lean_nat_abs(v_val_1088_);
                            v_one_1100_ = lean_unsigned_to_nat(1);
                            v_a_1101_ = lean_nat_sub(v_abs_1099_, v_one_1100_);
                            lean_dec(v_abs_1099_);
                            v___x_1102_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                            v___x_1103_ = lean_nat_add(v_a_1101_, v_one_1100_);
                            lean_dec(v_a_1101_);
                            v___x_1104_ = l_Nat_reprFast(v___x_1103_);
                            v___x_1105_ = lean_string_append(v___x_1102_, v___x_1104_);
                            lean_dec_ref(v___x_1104_);
                            v___y_1091_ = v___x_1105_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_upperBound_1106_ = lean_ctor_get(v_x_1078_, 1);
                    if lean_obj_tag(v_upperBound_1106_) == 0 {
                        v_val_1107_ = lean_ctor_get(v_lowerBound_1085_, 0);
                        v___x_1108_ = l_Lean_Omega_Constraint_instToString___private__1___closed__3;
                        v_intZero_1114_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                        v_isNeg_1115_ = lean_int_dec_lt(v_val_1107_, v_intZero_1114_);
                        if v_isNeg_1115_ == 0 {
                            v_a_1116_ = lean_nat_abs(v_val_1107_);
                            v___x_1117_ = l_Nat_reprFast(v_a_1116_);
                            v___y_1110_ = v___x_1117_;
                            state = 3;
                            continue;
                        } else {
                            v_abs_1118_ = lean_nat_abs(v_val_1107_);
                            v_one_1119_ = lean_unsigned_to_nat(1);
                            v_a_1120_ = lean_nat_sub(v_abs_1118_, v_one_1119_);
                            lean_dec(v_abs_1118_);
                            v___x_1121_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                            v___x_1122_ = lean_nat_add(v_a_1120_, v_one_1119_);
                            lean_dec(v_a_1120_);
                            v___x_1123_ = l_Nat_reprFast(v___x_1122_);
                            v___x_1124_ = lean_string_append(v___x_1121_, v___x_1123_);
                            lean_dec_ref(v___x_1123_);
                            v___y_1110_ = v___x_1124_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_val_1125_ = lean_ctor_get(v_lowerBound_1085_, 0);
                        v_val_1126_ = lean_ctor_get(v_upperBound_1106_, 0);
                        v___x_1127_ = lean_int_dec_lt(v_val_1126_, v_val_1125_);
                        if v___x_1127_ == 0 {
                            v___x_1128_ = lean_int_dec_eq(v_val_1125_, v_val_1126_);
                            if v___x_1128_ == 0 {
                                v___x_1129_ =
                                    l_Lean_Omega_Constraint_instToString___private__1___closed__3;
                                v_intZero_1146_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                                v_isNeg_1147_ = lean_int_dec_lt(v_val_1125_, v_intZero_1146_);
                                if v_isNeg_1147_ == 0 {
                                    v_a_1148_ = lean_nat_abs(v_val_1125_);
                                    v___x_1149_ = l_Nat_reprFast(v_a_1148_);
                                    v___y_1131_ = v___x_1149_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_abs_1150_ = lean_nat_abs(v_val_1125_);
                                    v_one_1151_ = lean_unsigned_to_nat(1);
                                    v_a_1152_ = lean_nat_sub(v_abs_1150_, v_one_1151_);
                                    lean_dec(v_abs_1150_);
                                    v___x_1153_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                                    v___x_1154_ = lean_nat_add(v_a_1152_, v_one_1151_);
                                    lean_dec(v_a_1152_);
                                    v___x_1155_ = l_Nat_reprFast(v___x_1154_);
                                    v___x_1156_ = lean_string_append(v___x_1153_, v___x_1155_);
                                    lean_dec_ref(v___x_1155_);
                                    v___y_1131_ = v___x_1156_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___x_1157_ =
                                    l_Lean_Omega_Constraint_instToString___private__1___closed__6;
                                v_intZero_1163_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                                v_isNeg_1164_ = lean_int_dec_lt(v_val_1125_, v_intZero_1163_);
                                if v_isNeg_1164_ == 0 {
                                    v_a_1165_ = lean_nat_abs(v_val_1125_);
                                    v___x_1166_ = l_Nat_reprFast(v_a_1165_);
                                    v___y_1159_ = v___x_1166_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_abs_1167_ = lean_nat_abs(v_val_1125_);
                                    v_one_1168_ = lean_unsigned_to_nat(1);
                                    v_a_1169_ = lean_nat_sub(v_abs_1167_, v_one_1168_);
                                    lean_dec(v_abs_1167_);
                                    v___x_1170_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                                    v___x_1171_ = lean_nat_add(v_a_1169_, v_one_1168_);
                                    lean_dec(v_a_1169_);
                                    v___x_1172_ = l_Nat_reprFast(v___x_1171_);
                                    v___x_1173_ = lean_string_append(v___x_1170_, v___x_1172_);
                                    lean_dec_ref(v___x_1172_);
                                    v___y_1159_ = v___x_1173_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1174_ =
                                l_Lean_Omega_Constraint_instToString___private__1___closed__8;
                            return v___x_1174_;
                        }
                    }
                }
            }
            1 => {
                v___x_1082_ = lean_string_append(v___y_1080_, v___y_1081_);
                lean_dec_ref(v___y_1081_);
                v___x_1083_ = l_Lean_Omega_Constraint_instToString___private__1___closed__0;
                v___x_1084_ = lean_string_append(v___x_1082_, v___x_1083_);
                return v___x_1084_;
            }
            2 => {
                v___x_1092_ = lean_string_append(v___x_1089_, v___y_1091_);
                lean_dec_ref(v___y_1091_);
                v___x_1093_ = l_Lean_Omega_Constraint_instToString___private__1___closed__0;
                v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
                return v___x_1094_;
            }
            3 => {
                v___x_1111_ = lean_string_append(v___x_1108_, v___y_1110_);
                lean_dec_ref(v___y_1110_);
                v___x_1112_ = l_Lean_Omega_Constraint_instToString___private__1___closed__4;
                v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
                return v___x_1113_;
            }
            4 => {
                v___x_1132_ = lean_string_append(v___x_1129_, v___y_1131_);
                lean_dec_ref(v___y_1131_);
                v___x_1133_ = l_Lean_Omega_Constraint_instToString___private__1___closed__5;
                v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
                v_intZero_1135_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v_isNeg_1136_ = lean_int_dec_lt(v_val_1126_, v_intZero_1135_);
                if v_isNeg_1136_ == 0 {
                    v_a_1137_ = lean_nat_abs(v_val_1126_);
                    v___x_1138_ = l_Nat_reprFast(v_a_1137_);
                    v___y_1080_ = v___x_1134_;
                    v___y_1081_ = v___x_1138_;
                    state = 1;
                    continue;
                } else {
                    v_abs_1139_ = lean_nat_abs(v_val_1126_);
                    v_one_1140_ = lean_unsigned_to_nat(1);
                    v_a_1141_ = lean_nat_sub(v_abs_1139_, v_one_1140_);
                    lean_dec(v_abs_1139_);
                    v___x_1142_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                    v___x_1143_ = lean_nat_add(v_a_1141_, v_one_1140_);
                    lean_dec(v_a_1141_);
                    v___x_1144_ = l_Nat_reprFast(v___x_1143_);
                    v___x_1145_ = lean_string_append(v___x_1142_, v___x_1144_);
                    lean_dec_ref(v___x_1144_);
                    v___y_1080_ = v___x_1134_;
                    v___y_1081_ = v___x_1145_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1160_ = lean_string_append(v___x_1157_, v___y_1159_);
                lean_dec_ref(v___y_1159_);
                v___x_1161_ = l_Lean_Omega_Constraint_instToString___private__1___closed__7;
                v___x_1162_ = lean_string_append(v___x_1160_, v___x_1161_);
                return v___x_1162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_instToString___private__1___boxed(
    mut v_x_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1176_: *mut LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Lean_Omega_Constraint_instToString___private__1(v_x_1175_);
    lean_dec_ref(v_x_1175_);
    return v_res_1176_;
}
pub unsafe fn l_Lean_Omega_Constraint_sat(
    mut v_c_1179_: *mut LeanObject,
    mut v_t_1180_: *mut LeanObject,
) -> u8 {
    let mut v_lowerBound_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: u8 = 0;
    let mut v_val_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: u8 = 0;
    let mut v___x_1187_: u8 = 0;
    let mut v_val_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1181_ = lean_ctor_get(v_c_1179_, 0);
                v_upperBound_1182_ = lean_ctor_get(v_c_1179_, 1);
                if lean_obj_tag(v_lowerBound_1181_) == 0 {
                    v___x_1187_ = 1;
                    v___y_1184_ = v___x_1187_;
                    state = 1;
                    continue;
                } else {
                    v_val_1188_ = lean_ctor_get(v_lowerBound_1181_, 0);
                    v___x_1189_ = lean_int_dec_le(v_val_1188_, v_t_1180_);
                    if v___x_1189_ == 0 {
                        return v___x_1189_;
                    } else {
                        v___y_1184_ = v___x_1189_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_upperBound_1182_) == 0 {
                    return v___y_1184_;
                } else {
                    v_val_1185_ = lean_ctor_get(v_upperBound_1182_, 0);
                    v___x_1186_ = lean_int_dec_le(v_t_1180_, v_val_1185_);
                    if v___x_1186_ == 0 {
                        return v___x_1186_;
                    } else {
                        return v___y_1184_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_sat___boxed(
    mut v_c_1190_: *mut LeanObject,
    mut v_t_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1192_: u8 = 0;
    let mut v_r_1193_: *mut LeanObject = core::ptr::null_mut();
    v_res_1192_ = l_Lean_Omega_Constraint_sat(v_c_1190_, v_t_1191_);
    lean_dec(v_t_1191_);
    lean_dec_ref(v_c_1190_);
    v_r_1193_ = lean_box((v_res_1192_) as usize);
    return v_r_1193_;
}
pub unsafe fn l_Lean_Omega_Constraint_map(
    mut v_c_1194_: *mut LeanObject,
    mut v_f_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1200_: u8 = 0;
    let mut v___y_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_val_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1196_ = lean_ctor_get(v_c_1194_, 0);
                v_upperBound_1197_ = lean_ctor_get(v_c_1194_, 1);
                v_isSharedCheck_1227_ = (!lean_is_exclusive(v_c_1194_)) as u8;
                if v_isSharedCheck_1227_ == 0 {
                    v___x_1199_ = v_c_1194_;
                    v_isShared_1200_ = v_isSharedCheck_1227_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upperBound_1197_);
                    lean_inc(v_lowerBound_1196_);
                    lean_dec(v_c_1194_);
                    v___x_1199_ = lean_box(0);
                    v_isShared_1200_ = v_isSharedCheck_1227_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_lowerBound_1196_) == 0 {
                    v___y_1202_ = v_lowerBound_1196_;
                    state = 2;
                    continue;
                } else {
                    v_val_1218_ = lean_ctor_get(v_lowerBound_1196_, 0);
                    v_isSharedCheck_1226_ = (!lean_is_exclusive(v_lowerBound_1196_)) as u8;
                    if v_isSharedCheck_1226_ == 0 {
                        v___x_1220_ = v_lowerBound_1196_;
                        v_isShared_1221_ = v_isSharedCheck_1226_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_1218_);
                        lean_dec(v_lowerBound_1196_);
                        v___x_1220_ = lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1226_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_upperBound_1197_) == 0 {
                    lean_dec_ref(v_f_1195_);
                    if v_isShared_1200_ == 0 {
                        lean_ctor_set(v___x_1199_, 0, v___y_1202_);
                        v___x_1204_ = v___x_1199_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___y_1202_);
                        lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_upperBound_1197_);
                        v___x_1204_ = v_reuseFailAlloc_1205_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1206_ = lean_ctor_get(v_upperBound_1197_, 0);
                    v_isSharedCheck_1217_ = (!lean_is_exclusive(v_upperBound_1197_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1208_ = v_upperBound_1197_;
                        v_isShared_1209_ = v_isSharedCheck_1217_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_1206_);
                        lean_dec(v_upperBound_1197_);
                        v___x_1208_ = lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1217_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1204_;
            }
            4 => {
                v___x_1210_ = lean_apply_1(v_f_1195_, v_val_1206_);
                if v_isShared_1209_ == 0 {
                    lean_ctor_set(v___x_1208_, 0, v___x_1210_);
                    v___x_1212_ = v___x_1208_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1210_);
                    v___x_1212_ = v_reuseFailAlloc_1216_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1200_ == 0 {
                    lean_ctor_set(v___x_1199_, 1, v___x_1212_);
                    lean_ctor_set(v___x_1199_, 0, v___y_1202_);
                    v___x_1214_ = v___x_1199_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___y_1202_);
                    lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
                    v___x_1214_ = v_reuseFailAlloc_1215_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1214_;
            }
            7 => {
                lean_inc_ref(v_f_1195_);
                v___x_1222_ = lean_apply_1(v_f_1195_, v_val_1218_);
                if v_isShared_1221_ == 0 {
                    lean_ctor_set(v___x_1220_, 0, v___x_1222_);
                    v___x_1224_ = v___x_1220_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_1202_ = v___x_1224_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_translate___lam__0(
    mut v_t_1228_: *mut LeanObject,
    mut v_x_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    v___x_1230_ = lean_int_add(v_x_1229_, v_t_1228_);
    return v___x_1230_;
}
pub unsafe fn l_Lean_Omega_Constraint_translate___lam__0___boxed(
    mut v_t_1231_: *mut LeanObject,
    mut v_x_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1233_: *mut LeanObject = core::ptr::null_mut();
    v_res_1233_ = l_Lean_Omega_Constraint_translate___lam__0(v_t_1231_, v_x_1232_);
    lean_dec(v_x_1232_);
    lean_dec(v_t_1231_);
    return v_res_1233_;
}
pub unsafe fn l_Lean_Omega_Constraint_translate(
    mut v_c_1234_: *mut LeanObject,
    mut v_t_1235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    v___f_1236_ = lean_alloc_closure(
        l_Lean_Omega_Constraint_translate___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1236_, 0, v_t_1235_);
    v___x_1237_ = l_Lean_Omega_Constraint_map(v_c_1234_, v___f_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_Omega_Constraint_flip(mut v_c_1238_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lowerBound_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1239_ = lean_ctor_get(v_c_1238_, 0);
                v_upperBound_1240_ = lean_ctor_get(v_c_1238_, 1);
                v_isSharedCheck_1247_ = (!lean_is_exclusive(v_c_1238_)) as u8;
                if v_isSharedCheck_1247_ == 0 {
                    v___x_1242_ = v_c_1238_;
                    v_isShared_1243_ = v_isSharedCheck_1247_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upperBound_1240_);
                    lean_inc(v_lowerBound_1239_);
                    lean_dec(v_c_1238_);
                    v___x_1242_ = lean_box(0);
                    v_isShared_1243_ = v_isSharedCheck_1247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1243_ == 0 {
                    lean_ctor_set(v___x_1242_, 1, v_lowerBound_1239_);
                    lean_ctor_set(v___x_1242_, 0, v_upperBound_1240_);
                    v___x_1245_ = v___x_1242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_upperBound_1240_);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_lowerBound_1239_);
                    v___x_1245_ = v_reuseFailAlloc_1246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_neg(mut v_c_1249_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___f_1250_ = l_Lean_Omega_Constraint_neg___closed__0;
    v___x_1251_ = l_Lean_Omega_Constraint_flip(v_c_1249_);
    v___x_1252_ = l_Lean_Omega_Constraint_map(v___x_1251_, v___f_1250_);
    return v___x_1252_;
}
pub unsafe fn _init_l_Lean_Omega_Constraint_impossible___closed__0() -> *mut LeanObject {
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v___x_1256_ = lean_unsigned_to_nat(1);
    v___x_1257_ = lean_nat_to_int(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn _init_l_Lean_Omega_Constraint_impossible___closed__1() -> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__0_once),
        _init_l_Lean_Omega_Constraint_impossible___closed__0,
    );
    v___x_1259_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1259_, 0, v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn _init_l_Lean_Omega_Constraint_impossible___closed__2() -> *mut LeanObject {
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1260_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
    v___x_1261_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1261_, 0, v___x_1260_);
    return v___x_1261_;
}
pub unsafe fn _init_l_Lean_Omega_Constraint_impossible___closed__3() -> *mut LeanObject {
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v___x_1262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__2_once),
        _init_l_Lean_Omega_Constraint_impossible___closed__2,
    );
    v___x_1263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__1_once),
        _init_l_Lean_Omega_Constraint_impossible___closed__1,
    );
    v___x_1264_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    lean_ctor_set(v___x_1264_, 1, v___x_1262_);
    return v___x_1264_;
}
pub unsafe fn _init_l_Lean_Omega_Constraint_impossible() -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___x_1265_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__3_once),
        _init_l_Lean_Omega_Constraint_impossible___closed__3,
    );
    return v___x_1265_;
}
pub unsafe fn l_Lean_Omega_Constraint_exact(mut v_r_1266_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    v___x_1267_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1267_, 0, v_r_1266_);
    lean_inc_ref(v___x_1267_);
    v___x_1268_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    lean_ctor_set(v___x_1268_, 1, v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Lean_Omega_Constraint_isImpossible(mut v_x_1269_: *mut LeanObject) -> u8 {
    let mut v_lowerBound_1270_: *mut LeanObject = core::ptr::null_mut();
    v_lowerBound_1270_ = lean_ctor_get(v_x_1269_, 0);
    if lean_obj_tag(v_lowerBound_1270_) == 1 {
        let mut v_upperBound_1271_: *mut LeanObject = core::ptr::null_mut();
        v_upperBound_1271_ = lean_ctor_get(v_x_1269_, 1);
        if lean_obj_tag(v_upperBound_1271_) == 1 {
            let mut v_val_1272_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1273_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1274_: u8 = 0;
            v_val_1272_ = lean_ctor_get(v_lowerBound_1270_, 0);
            v_val_1273_ = lean_ctor_get(v_upperBound_1271_, 0);
            v___x_1274_ = lean_int_dec_lt(v_val_1273_, v_val_1272_);
            return v___x_1274_;
        } else {
            let mut v___x_1275_: u8 = 0;
            v___x_1275_ = 0;
            return v___x_1275_;
        }
    } else {
        let mut v___x_1276_: u8 = 0;
        v___x_1276_ = 0;
        return v___x_1276_;
    }
}
pub unsafe fn l_Lean_Omega_Constraint_isImpossible___boxed(
    mut v_x_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1278_: u8 = 0;
    let mut v_r_1279_: *mut LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lean_Omega_Constraint_isImpossible(v_x_1277_);
    lean_dec_ref(v_x_1277_);
    v_r_1279_ = lean_box((v_res_1278_) as usize);
    return v_r_1279_;
}
pub unsafe fn l_Lean_Omega_Constraint_isExact(mut v_x_1280_: *mut LeanObject) -> u8 {
    let mut v_lowerBound_1281_: *mut LeanObject = core::ptr::null_mut();
    v_lowerBound_1281_ = lean_ctor_get(v_x_1280_, 0);
    if lean_obj_tag(v_lowerBound_1281_) == 1 {
        let mut v_upperBound_1282_: *mut LeanObject = core::ptr::null_mut();
        v_upperBound_1282_ = lean_ctor_get(v_x_1280_, 1);
        if lean_obj_tag(v_upperBound_1282_) == 1 {
            let mut v_val_1283_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1284_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1285_: u8 = 0;
            v_val_1283_ = lean_ctor_get(v_lowerBound_1281_, 0);
            v_val_1284_ = lean_ctor_get(v_upperBound_1282_, 0);
            v___x_1285_ = lean_int_dec_eq(v_val_1283_, v_val_1284_);
            return v___x_1285_;
        } else {
            let mut v___x_1286_: u8 = 0;
            v___x_1286_ = 0;
            return v___x_1286_;
        }
    } else {
        let mut v___x_1287_: u8 = 0;
        v___x_1287_ = 0;
        return v___x_1287_;
    }
}
pub unsafe fn l_Lean_Omega_Constraint_isExact___boxed(
    mut v_x_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: u8 = 0;
    let mut v_r_1290_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Lean_Omega_Constraint_isExact(v_x_1288_);
    lean_dec_ref(v_x_1288_);
    v_r_1290_ = lean_box((v_res_1289_) as usize);
    return v_r_1290_;
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter___redArg(
    mut v_x_1291_: *mut LeanObject,
    mut v_h__1_1292_: *mut LeanObject,
    mut v_h__2_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1294_: *mut LeanObject = core::ptr::null_mut();
    v_lowerBound_1294_ = lean_ctor_get(v_x_1291_, 0);
    if lean_obj_tag(v_lowerBound_1294_) == 1 {
        let mut v_upperBound_1295_: *mut LeanObject = core::ptr::null_mut();
        v_upperBound_1295_ = lean_ctor_get(v_x_1291_, 1);
        if lean_obj_tag(v_upperBound_1295_) == 1 {
            let mut v_val_1296_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1297_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_upperBound_1295_);
            lean_inc_ref(v_lowerBound_1294_);
            lean_dec(v_h__2_1293_);
            lean_dec_ref(v_x_1291_);
            v_val_1296_ = lean_ctor_get(v_lowerBound_1294_, 0);
            lean_inc(v_val_1296_);
            lean_dec_ref_known(v_lowerBound_1294_, 1);
            v_val_1297_ = lean_ctor_get(v_upperBound_1295_, 0);
            lean_inc(v_val_1297_);
            lean_dec_ref_known(v_upperBound_1295_, 1);
            v___x_1298_ = lean_apply_2(v_h__1_1292_, v_val_1296_, v_val_1297_);
            return v___x_1298_;
        } else {
            let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1292_);
            v___x_1299_ = lean_apply_2(v_h__2_1293_, v_x_1291_, lean_box(0));
            return v___x_1299_;
        }
    } else {
        let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1292_);
        v___x_1300_ = lean_apply_2(v_h__2_1293_, v_x_1291_, lean_box(0));
        return v___x_1300_;
    }
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter(
    mut v_motive_1301_: *mut LeanObject,
    mut v_x_1302_: *mut LeanObject,
    mut v_h__1_1303_: *mut LeanObject,
    mut v_h__2_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1305_: *mut LeanObject = core::ptr::null_mut();
    v_lowerBound_1305_ = lean_ctor_get(v_x_1302_, 0);
    if lean_obj_tag(v_lowerBound_1305_) == 1 {
        let mut v_upperBound_1306_: *mut LeanObject = core::ptr::null_mut();
        v_upperBound_1306_ = lean_ctor_get(v_x_1302_, 1);
        if lean_obj_tag(v_upperBound_1306_) == 1 {
            let mut v_val_1307_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1308_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_upperBound_1306_);
            lean_inc_ref(v_lowerBound_1305_);
            lean_dec(v_h__2_1304_);
            lean_dec_ref(v_x_1302_);
            v_val_1307_ = lean_ctor_get(v_lowerBound_1305_, 0);
            lean_inc(v_val_1307_);
            lean_dec_ref_known(v_lowerBound_1305_, 1);
            v_val_1308_ = lean_ctor_get(v_upperBound_1306_, 0);
            lean_inc(v_val_1308_);
            lean_dec_ref_known(v_upperBound_1306_, 1);
            v___x_1309_ = lean_apply_2(v_h__1_1303_, v_val_1307_, v_val_1308_);
            return v___x_1309_;
        } else {
            let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1303_);
            v___x_1310_ = lean_apply_2(v_h__2_1304_, v_x_1302_, lean_box(0));
            return v___x_1310_;
        }
    } else {
        let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1303_);
        v___x_1311_ = lean_apply_2(v_h__2_1304_, v_x_1302_, lean_box(0));
        return v___x_1311_;
    }
}
pub unsafe fn l_Lean_Omega_Constraint_scale___lam__0(
    mut v_k_1312_: *mut LeanObject,
    mut v_x_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v___x_1314_ = lean_int_mul(v_k_1312_, v_x_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Lean_Omega_Constraint_scale___lam__0___boxed(
    mut v_k_1315_: *mut LeanObject,
    mut v_x_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1317_: *mut LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lean_Omega_Constraint_scale___lam__0(v_k_1315_, v_x_1316_);
    lean_dec(v_x_1316_);
    lean_dec(v_k_1315_);
    return v_res_1317_;
}
pub unsafe fn _init_l_Lean_Omega_Constraint_scale___closed__0() -> *mut LeanObject {
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    v___x_1318_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__2_once),
        _init_l_Lean_Omega_Constraint_impossible___closed__2,
    );
    v___x_1319_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1319_, 0, v___x_1318_);
    lean_ctor_set(v___x_1319_, 1, v___x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Lean_Omega_Constraint_scale(
    mut v_k_1320_: *mut LeanObject,
    mut v_c_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    v___x_1322_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
    v___x_1323_ = lean_int_dec_eq(v_k_1320_, v___x_1322_);
    if v___x_1323_ == 0 {
        let mut v___x_1324_: u8 = 0;
        v___x_1324_ = lean_int_dec_lt(v___x_1322_, v_k_1320_);
        if v___x_1324_ == 0 {
            let mut v___f_1325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
            v___f_1325_ = lean_alloc_closure(
                l_Lean_Omega_Constraint_scale___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_1325_, 0, v_k_1320_);
            v___x_1326_ = l_Lean_Omega_Constraint_flip(v_c_1321_);
            v___x_1327_ = l_Lean_Omega_Constraint_map(v___x_1326_, v___f_1325_);
            return v___x_1327_;
        } else {
            let mut v___f_1328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
            v___f_1328_ = lean_alloc_closure(
                l_Lean_Omega_Constraint_scale___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_1328_, 0, v_k_1320_);
            v___x_1329_ = l_Lean_Omega_Constraint_map(v_c_1321_, v___f_1328_);
            return v___x_1329_;
        }
    } else {
        let mut v___x_1330_: u8 = 0;
        lean_dec(v_k_1320_);
        v___x_1330_ = l_Lean_Omega_Constraint_isImpossible(v_c_1321_);
        if v___x_1330_ == 0 {
            let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_c_1321_);
            v___x_1331_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_scale___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_scale___closed__0_once),
                _init_l_Lean_Omega_Constraint_scale___closed__0,
            );
            return v___x_1331_;
        } else {
            return v_c_1321_;
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_add(
    mut v_x_1332_: *mut LeanObject,
    mut v_y_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___y_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut v_unused_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowerBound_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1376_: u8 = 0;
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1334_ = lean_ctor_get(v_x_1332_, 0);
                v_upperBound_1335_ = lean_ctor_get(v_x_1332_, 1);
                v_isSharedCheck_1377_ = (!lean_is_exclusive(v_x_1332_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v___x_1337_ = v_x_1332_;
                    v_isShared_1338_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upperBound_1335_);
                    lean_inc(v_lowerBound_1334_);
                    lean_dec(v_x_1332_);
                    v___x_1337_ = lean_box(0);
                    v_isShared_1338_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_lowerBound_1334_) == 0 {
                    v___y_1340_ = v_lowerBound_1334_;
                    state = 2;
                    continue;
                } else {
                    v_lowerBound_1366_ = lean_ctor_get(v_y_1333_, 0);
                    lean_inc(v_lowerBound_1366_);
                    if lean_obj_tag(v_lowerBound_1366_) == 0 {
                        lean_dec_ref_known(v_lowerBound_1334_, 1);
                        v___y_1340_ = v_lowerBound_1366_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1367_ = lean_ctor_get(v_lowerBound_1334_, 0);
                        lean_inc(v_val_1367_);
                        lean_dec_ref_known(v_lowerBound_1334_, 1);
                        v_val_1368_ = lean_ctor_get(v_lowerBound_1366_, 0);
                        v_isSharedCheck_1376_ = (!lean_is_exclusive(v_lowerBound_1366_)) as u8;
                        if v_isSharedCheck_1376_ == 0 {
                            v___x_1370_ = v_lowerBound_1366_;
                            v_isShared_1371_ = v_isSharedCheck_1376_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_val_1368_);
                            lean_dec(v_lowerBound_1366_);
                            v___x_1370_ = lean_box(0);
                            v_isShared_1371_ = v_isSharedCheck_1376_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_upperBound_1335_) == 0 {
                    lean_dec_ref(v_y_1333_);
                    if v_isShared_1338_ == 0 {
                        lean_ctor_set(v___x_1337_, 0, v___y_1340_);
                        v___x_1342_ = v___x_1337_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___y_1340_);
                        lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_upperBound_1335_);
                        v___x_1342_ = v_reuseFailAlloc_1343_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1337_);
                    v_upperBound_1344_ = lean_ctor_get(v_y_1333_, 1);
                    v_isSharedCheck_1364_ = (!lean_is_exclusive(v_y_1333_)) as u8;
                    if v_isSharedCheck_1364_ == 0 {
                        v_unused_1365_ = lean_ctor_get(v_y_1333_, 0);
                        lean_dec(v_unused_1365_);
                        v___x_1346_ = v_y_1333_;
                        v_isShared_1347_ = v_isSharedCheck_1364_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1344_);
                        lean_dec(v_y_1333_);
                        v___x_1346_ = lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1364_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1342_;
            }
            4 => {
                if lean_obj_tag(v_upperBound_1344_) == 0 {
                    lean_dec_ref_known(v_upperBound_1335_, 1);
                    if v_isShared_1347_ == 0 {
                        lean_ctor_set(v___x_1346_, 0, v___y_1340_);
                        v___x_1349_ = v___x_1346_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___y_1340_);
                        lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_upperBound_1344_);
                        v___x_1349_ = v_reuseFailAlloc_1350_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_1351_ = lean_ctor_get(v_upperBound_1335_, 0);
                    lean_inc(v_val_1351_);
                    lean_dec_ref_known(v_upperBound_1335_, 1);
                    v_val_1352_ = lean_ctor_get(v_upperBound_1344_, 0);
                    v_isSharedCheck_1363_ = (!lean_is_exclusive(v_upperBound_1344_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1354_ = v_upperBound_1344_;
                        v_isShared_1355_ = v_isSharedCheck_1363_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_1352_);
                        lean_dec(v_upperBound_1344_);
                        v___x_1354_ = lean_box(0);
                        v_isShared_1355_ = v_isSharedCheck_1363_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1349_;
            }
            6 => {
                v___x_1356_ = lean_int_add(v_val_1351_, v_val_1352_);
                lean_dec(v_val_1352_);
                lean_dec(v_val_1351_);
                if v_isShared_1355_ == 0 {
                    lean_ctor_set(v___x_1354_, 0, v___x_1356_);
                    v___x_1358_ = v___x_1354_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1356_);
                    v___x_1358_ = v_reuseFailAlloc_1362_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1347_ == 0 {
                    lean_ctor_set(v___x_1346_, 1, v___x_1358_);
                    lean_ctor_set(v___x_1346_, 0, v___y_1340_);
                    v___x_1360_ = v___x_1346_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___y_1340_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1358_);
                    v___x_1360_ = v_reuseFailAlloc_1361_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1360_;
            }
            9 => {
                v___x_1372_ = lean_int_add(v_val_1367_, v_val_1368_);
                lean_dec(v_val_1368_);
                lean_dec(v_val_1367_);
                if v_isShared_1371_ == 0 {
                    lean_ctor_set(v___x_1370_, 0, v___x_1372_);
                    v___x_1374_ = v___x_1370_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1340_ = v___x_1374_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_combo(
    mut v_a_1378_: *mut LeanObject,
    mut v_x_1379_: *mut LeanObject,
    mut v_b_1380_: *mut LeanObject,
    mut v_y_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    v___x_1382_ = l_Lean_Omega_Constraint_scale(v_a_1378_, v_x_1379_);
    v___x_1383_ = l_Lean_Omega_Constraint_scale(v_b_1380_, v_y_1381_);
    v___x_1384_ = l_Lean_Omega_Constraint_add(v___x_1382_, v___x_1383_);
    return v___x_1384_;
}
pub unsafe fn l_Lean_Omega_Constraint_combine___lam__0(
    mut v_x_1385_: *mut LeanObject,
    mut v_y_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1387_: u8 = 0;
    v___x_1387_ = lean_int_dec_le(v_x_1385_, v_y_1386_);
    if v___x_1387_ == 0 {
        lean_inc(v_x_1385_);
        return v_x_1385_;
    } else {
        lean_inc(v_y_1386_);
        return v_y_1386_;
    }
}
pub unsafe fn l_Lean_Omega_Constraint_combine___lam__0___boxed(
    mut v_x_1388_: *mut LeanObject,
    mut v_y_1389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1390_: *mut LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Lean_Omega_Constraint_combine___lam__0(v_x_1388_, v_y_1389_);
    lean_dec(v_y_1389_);
    lean_dec(v_x_1388_);
    return v_res_1390_;
}
pub unsafe fn l_Lean_Omega_Constraint_combine___lam__1(
    mut v_x_1391_: *mut LeanObject,
    mut v_y_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: u8 = 0;
    v___x_1393_ = lean_int_dec_le(v_x_1391_, v_y_1392_);
    if v___x_1393_ == 0 {
        lean_inc(v_y_1392_);
        return v_y_1392_;
    } else {
        lean_inc(v_x_1391_);
        return v_x_1391_;
    }
}
pub unsafe fn l_Lean_Omega_Constraint_combine___lam__1___boxed(
    mut v_x_1394_: *mut LeanObject,
    mut v_y_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_Omega_Constraint_combine___lam__1(v_x_1394_, v_y_1395_);
    lean_dec(v_y_1395_);
    lean_dec(v_x_1394_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_Omega_Constraint_combine(
    mut v_x_1399_: *mut LeanObject,
    mut v_y_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowerBound_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___f_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1401_ = lean_ctor_get(v_x_1399_, 0);
                lean_inc(v_lowerBound_1401_);
                v_upperBound_1402_ = lean_ctor_get(v_x_1399_, 1);
                lean_inc(v_upperBound_1402_);
                lean_dec_ref(v_x_1399_);
                v_lowerBound_1403_ = lean_ctor_get(v_y_1400_, 0);
                v_upperBound_1404_ = lean_ctor_get(v_y_1400_, 1);
                v_isSharedCheck_1415_ = (!lean_is_exclusive(v_y_1400_)) as u8;
                if v_isSharedCheck_1415_ == 0 {
                    v___x_1406_ = v_y_1400_;
                    v_isShared_1407_ = v_isSharedCheck_1415_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upperBound_1404_);
                    lean_inc(v_lowerBound_1403_);
                    lean_dec(v_y_1400_);
                    v___x_1406_ = lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1415_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1408_ = l_Lean_Omega_Constraint_combine___closed__0;
                v___f_1409_ = l_Lean_Omega_Constraint_combine___closed__1;
                v___x_1410_ =
                    l_Option_merge___redArg(v___f_1408_, v_lowerBound_1401_, v_lowerBound_1403_);
                v___x_1411_ =
                    l_Option_merge___redArg(v___f_1409_, v_upperBound_1402_, v_upperBound_1404_);
                if v_isShared_1407_ == 0 {
                    lean_ctor_set(v___x_1406_, 1, v___x_1411_);
                    lean_ctor_set(v___x_1406_, 0, v___x_1410_);
                    v___x_1413_ = v___x_1406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1411_);
                    v___x_1413_ = v_reuseFailAlloc_1414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter___redArg(
    mut v_x_1416_: *mut LeanObject,
    mut v_x_1417_: *mut LeanObject,
    mut v_h__1_1418_: *mut LeanObject,
    mut v_h__2_1419_: *mut LeanObject,
    mut v_h__3_1420_: *mut LeanObject,
    mut v_h__4_1421_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1416_) == 0 {
        lean_dec(v_h__4_1421_);
        lean_dec(v_h__2_1419_);
        if lean_obj_tag(v_x_1417_) == 0 {
            let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1420_);
            v___x_1422_ = lean_box(0);
            v___x_1423_ = lean_apply_1(v_h__1_1418_, v___x_1422_);
            return v___x_1423_;
        } else {
            let mut v_val_1424_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1418_);
            v_val_1424_ = lean_ctor_get(v_x_1417_, 0);
            lean_inc(v_val_1424_);
            lean_dec_ref_known(v_x_1417_, 1);
            v___x_1425_ = lean_apply_1(v_h__3_1420_, v_val_1424_);
            return v___x_1425_;
        }
    } else {
        lean_dec(v_h__3_1420_);
        lean_dec(v_h__1_1418_);
        if lean_obj_tag(v_x_1417_) == 0 {
            let mut v_val_1426_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1421_);
            v_val_1426_ = lean_ctor_get(v_x_1416_, 0);
            lean_inc(v_val_1426_);
            lean_dec_ref_known(v_x_1416_, 1);
            v___x_1427_ = lean_apply_1(v_h__2_1419_, v_val_1426_);
            return v___x_1427_;
        } else {
            let mut v_val_1428_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1429_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1419_);
            v_val_1428_ = lean_ctor_get(v_x_1416_, 0);
            lean_inc(v_val_1428_);
            lean_dec_ref_known(v_x_1416_, 1);
            v_val_1429_ = lean_ctor_get(v_x_1417_, 0);
            lean_inc(v_val_1429_);
            lean_dec_ref_known(v_x_1417_, 1);
            v___x_1430_ = lean_apply_2(v_h__4_1421_, v_val_1428_, v_val_1429_);
            return v___x_1430_;
        }
    }
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter(
    mut v_00_u03b1_1431_: *mut LeanObject,
    mut v_motive_1432_: *mut LeanObject,
    mut v_x_1433_: *mut LeanObject,
    mut v_x_1434_: *mut LeanObject,
    mut v_h__1_1435_: *mut LeanObject,
    mut v_h__2_1436_: *mut LeanObject,
    mut v_h__3_1437_: *mut LeanObject,
    mut v_h__4_1438_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1433_) == 0 {
        lean_dec(v_h__4_1438_);
        lean_dec(v_h__2_1436_);
        if lean_obj_tag(v_x_1434_) == 0 {
            let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1437_);
            v___x_1439_ = lean_box(0);
            v___x_1440_ = lean_apply_1(v_h__1_1435_, v___x_1439_);
            return v___x_1440_;
        } else {
            let mut v_val_1441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1435_);
            v_val_1441_ = lean_ctor_get(v_x_1434_, 0);
            lean_inc(v_val_1441_);
            lean_dec_ref_known(v_x_1434_, 1);
            v___x_1442_ = lean_apply_1(v_h__3_1437_, v_val_1441_);
            return v___x_1442_;
        }
    } else {
        lean_dec(v_h__3_1437_);
        lean_dec(v_h__1_1435_);
        if lean_obj_tag(v_x_1434_) == 0 {
            let mut v_val_1443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1438_);
            v_val_1443_ = lean_ctor_get(v_x_1433_, 0);
            lean_inc(v_val_1443_);
            lean_dec_ref_known(v_x_1433_, 1);
            v___x_1444_ = lean_apply_1(v_h__2_1436_, v_val_1443_);
            return v___x_1444_;
        } else {
            let mut v_val_1445_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1436_);
            v_val_1445_ = lean_ctor_get(v_x_1433_, 0);
            lean_inc(v_val_1445_);
            lean_dec_ref_known(v_x_1433_, 1);
            v_val_1446_ = lean_ctor_get(v_x_1434_, 0);
            lean_inc(v_val_1446_);
            lean_dec_ref_known(v_x_1434_, 1);
            v___x_1447_ = lean_apply_2(v_h__4_1438_, v_val_1445_, v_val_1446_);
            return v___x_1447_;
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_div(
    mut v_c_1448_: *mut LeanObject,
    mut v_k_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowerBound_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___y_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1472_: u8 = 0;
    let mut v_val_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1476_: u8 = 0;
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lowerBound_1450_ = lean_ctor_get(v_c_1448_, 0);
                v_upperBound_1451_ = lean_ctor_get(v_c_1448_, 1);
                v_isSharedCheck_1485_ = (!lean_is_exclusive(v_c_1448_)) as u8;
                if v_isSharedCheck_1485_ == 0 {
                    v___x_1453_ = v_c_1448_;
                    v_isShared_1454_ = v_isSharedCheck_1485_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upperBound_1451_);
                    lean_inc(v_lowerBound_1450_);
                    lean_dec(v_c_1448_);
                    v___x_1453_ = lean_box(0);
                    v_isShared_1454_ = v_isSharedCheck_1485_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_lowerBound_1450_) == 0 {
                    v___y_1456_ = v_lowerBound_1450_;
                    state = 2;
                    continue;
                } else {
                    v_val_1473_ = lean_ctor_get(v_lowerBound_1450_, 0);
                    v_isSharedCheck_1484_ = (!lean_is_exclusive(v_lowerBound_1450_)) as u8;
                    if v_isSharedCheck_1484_ == 0 {
                        v___x_1475_ = v_lowerBound_1450_;
                        v_isShared_1476_ = v_isSharedCheck_1484_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_1473_);
                        lean_dec(v_lowerBound_1450_);
                        v___x_1475_ = lean_box(0);
                        v_isShared_1476_ = v_isSharedCheck_1484_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_upperBound_1451_) == 0 {
                    lean_dec(v_k_1449_);
                    if v_isShared_1454_ == 0 {
                        lean_ctor_set(v___x_1453_, 0, v___y_1456_);
                        v___x_1458_ = v___x_1453_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___y_1456_);
                        lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_upperBound_1451_);
                        v___x_1458_ = v_reuseFailAlloc_1459_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1460_ = lean_ctor_get(v_upperBound_1451_, 0);
                    v_isSharedCheck_1472_ = (!lean_is_exclusive(v_upperBound_1451_)) as u8;
                    if v_isSharedCheck_1472_ == 0 {
                        v___x_1462_ = v_upperBound_1451_;
                        v_isShared_1463_ = v_isSharedCheck_1472_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_1460_);
                        lean_dec(v_upperBound_1451_);
                        v___x_1462_ = lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1472_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1458_;
            }
            4 => {
                v___x_1464_ = lean_nat_to_int(v_k_1449_);
                v___x_1465_ = lean_int_ediv(v_val_1460_, v___x_1464_);
                lean_dec(v___x_1464_);
                lean_dec(v_val_1460_);
                if v_isShared_1463_ == 0 {
                    lean_ctor_set(v___x_1462_, 0, v___x_1465_);
                    v___x_1467_ = v___x_1462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1465_);
                    v___x_1467_ = v_reuseFailAlloc_1471_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1454_ == 0 {
                    lean_ctor_set(v___x_1453_, 1, v___x_1467_);
                    lean_ctor_set(v___x_1453_, 0, v___y_1456_);
                    v___x_1469_ = v___x_1453_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___y_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1467_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1469_;
            }
            7 => {
                v___x_1477_ = lean_int_neg(v_val_1473_);
                lean_dec(v_val_1473_);
                lean_inc(v_k_1449_);
                v___x_1478_ = lean_nat_to_int(v_k_1449_);
                v___x_1479_ = lean_int_ediv(v___x_1477_, v___x_1478_);
                lean_dec(v___x_1478_);
                lean_dec(v___x_1477_);
                v___x_1480_ = lean_int_neg(v___x_1479_);
                lean_dec(v___x_1479_);
                if v_isShared_1476_ == 0 {
                    lean_ctor_set(v___x_1475_, 0, v___x_1480_);
                    v___x_1482_ = v___x_1475_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
                    v___x_1482_ = v_reuseFailAlloc_1483_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_1456_ = v___x_1482_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_Constraint_sat_x27(
    mut v_c_1486_: *mut LeanObject,
    mut v_x_1487_: *mut LeanObject,
    mut v_y_1488_: *mut LeanObject,
) -> u8 {
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    v___x_1489_ = l_Lean_Omega_IntList_dot(v_x_1487_, v_y_1488_);
    v___x_1490_ = l_Lean_Omega_Constraint_sat(v_c_1486_, v___x_1489_);
    lean_dec(v___x_1489_);
    return v___x_1490_;
}
pub unsafe fn l_Lean_Omega_Constraint_sat_x27___boxed(
    mut v_c_1491_: *mut LeanObject,
    mut v_x_1492_: *mut LeanObject,
    mut v_y_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1494_: u8 = 0;
    let mut v_r_1495_: *mut LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Lean_Omega_Constraint_sat_x27(v_c_1491_, v_x_1492_, v_y_1493_);
    lean_dec(v_x_1492_);
    lean_dec_ref(v_c_1491_);
    v_r_1495_ = lean_box((v_res_1494_) as usize);
    return v_r_1495_;
}
pub unsafe fn l_Lean_Omega_normalize_x3f(mut v_x_1496_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v_gcd_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1497_ = lean_ctor_get(v_x_1496_, 0);
                v_snd_1498_ = lean_ctor_get(v_x_1496_, 1);
                v_isSharedCheck_1527_ = (!lean_is_exclusive(v_x_1496_)) as u8;
                if v_isSharedCheck_1527_ == 0 {
                    v___x_1500_ = v_x_1496_;
                    v_isShared_1501_ = v_isSharedCheck_1527_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1498_);
                    lean_inc(v_fst_1497_);
                    lean_dec(v_x_1496_);
                    v___x_1500_ = lean_box(0);
                    v_isShared_1501_ = v_isSharedCheck_1527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gcd_1502_ = l_Lean_Omega_IntList_gcd(v_snd_1498_);
                v___x_1503_ = lean_unsigned_to_nat(0);
                v___x_1504_ = lean_nat_dec_eq(v_gcd_1502_, v___x_1503_);
                if v___x_1504_ == 0 {
                    v___x_1505_ = lean_unsigned_to_nat(1);
                    v___x_1506_ = lean_nat_dec_eq(v_gcd_1502_, v___x_1505_);
                    if v___x_1506_ == 0 {
                        lean_inc(v_gcd_1502_);
                        v___x_1507_ = l_Lean_Omega_Constraint_div(v_fst_1497_, v_gcd_1502_);
                        v___x_1508_ = lean_nat_to_int(v_gcd_1502_);
                        v___x_1509_ = l_Lean_Omega_IntList_sdiv(v_snd_1498_, v___x_1508_);
                        lean_dec(v___x_1508_);
                        if v_isShared_1501_ == 0 {
                            lean_ctor_set(v___x_1500_, 1, v___x_1509_);
                            lean_ctor_set(v___x_1500_, 0, v___x_1507_);
                            v___x_1511_ = v___x_1500_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1507_);
                            lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1509_);
                            v___x_1511_ = v_reuseFailAlloc_1513_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_gcd_1502_);
                        lean_del_object(v___x_1500_);
                        lean_dec(v_snd_1498_);
                        lean_dec(v_fst_1497_);
                        v___x_1514_ = lean_box(0);
                        return v___x_1514_;
                    }
                } else {
                    lean_dec(v_gcd_1502_);
                    v___x_1515_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                    v___x_1516_ = l_Lean_Omega_Constraint_sat(v_fst_1497_, v___x_1515_);
                    lean_dec(v_fst_1497_);
                    if v___x_1516_ == 0 {
                        v___x_1517_ = l_Lean_Omega_Constraint_impossible;
                        if v_isShared_1501_ == 0 {
                            lean_ctor_set(v___x_1500_, 0, v___x_1517_);
                            v___x_1519_ = v___x_1500_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1517_);
                            lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_snd_1498_);
                            v___x_1519_ = v_reuseFailAlloc_1521_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1522_ = l_Lean_Omega_Constraint_trivial;
                        if v_isShared_1501_ == 0 {
                            lean_ctor_set(v___x_1500_, 0, v___x_1522_);
                            v___x_1524_ = v___x_1500_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1522_);
                            lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_snd_1498_);
                            v___x_1524_ = v_reuseFailAlloc_1526_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1512_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1512_, 0, v___x_1511_);
                return v___x_1512_;
            }
            3 => {
                v___x_1520_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                return v___x_1520_;
            }
            4 => {
                v___x_1525_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1525_, 0, v___x_1524_);
                return v___x_1525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_normalize(mut v_p_1528_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_p_1528_);
    v___x_1529_ = l_Lean_Omega_normalize_x3f(v_p_1528_);
    if lean_obj_tag(v___x_1529_) == 0 {
        return v_p_1528_;
    } else {
        let mut v_val_1530_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_1528_);
        v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
        lean_inc(v_val_1530_);
        lean_dec_ref_known(v___x_1529_, 1);
        return v_val_1530_;
    }
}
pub unsafe fn _init_l_Lean_Omega_positivize_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    v___x_1531_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Omega_Constraint_impossible___closed__0_once),
        _init_l_Lean_Omega_Constraint_impossible___closed__0,
    );
    v___x_1532_ = lean_int_neg(v___x_1531_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_Omega_positivize_x3f(mut v_x_1533_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1534_ = lean_ctor_get(v_x_1533_, 0);
                v_snd_1535_ = lean_ctor_get(v_x_1533_, 1);
                v_isSharedCheck_1550_ = (!lean_is_exclusive(v_x_1533_)) as u8;
                if v_isSharedCheck_1550_ == 0 {
                    v___x_1537_ = v_x_1533_;
                    v_isShared_1538_ = v_isSharedCheck_1550_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1535_);
                    lean_inc(v_fst_1534_);
                    lean_dec(v_x_1533_);
                    v___x_1537_ = lean_box(0);
                    v_isShared_1538_ = v_isSharedCheck_1550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1539_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_1540_ = l_Lean_Omega_IntList_leading(v_snd_1535_);
                v___x_1541_ = lean_int_dec_le(v___x_1539_, v___x_1540_);
                lean_dec(v___x_1540_);
                if v___x_1541_ == 0 {
                    v___x_1542_ = l_Lean_Omega_Constraint_neg(v_fst_1534_);
                    v___x_1543_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Omega_positivize_x3f___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Omega_positivize_x3f___closed__0_once),
                        _init_l_Lean_Omega_positivize_x3f___closed__0,
                    );
                    v___x_1544_ = l_Lean_Omega_IntList_smul(v_snd_1535_, v___x_1543_);
                    if v_isShared_1538_ == 0 {
                        lean_ctor_set(v___x_1537_, 1, v___x_1544_);
                        lean_ctor_set(v___x_1537_, 0, v___x_1542_);
                        v___x_1546_ = v___x_1537_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
                        lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1544_);
                        v___x_1546_ = v_reuseFailAlloc_1548_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1537_);
                    lean_dec(v_snd_1535_);
                    lean_dec(v_fst_1534_);
                    v___x_1549_ = lean_box(0);
                    return v___x_1549_;
                }
            }
            2 => {
                v___x_1547_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1547_, 0, v___x_1546_);
                return v___x_1547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_tidy_x3f(mut v_x_1551_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1557_: u8 = 0;
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_x_1551_);
                v___x_1552_ = l_Lean_Omega_positivize_x3f(v_x_1551_);
                if lean_obj_tag(v___x_1552_) == 0 {
                    v___x_1553_ = l_Lean_Omega_normalize_x3f(v_x_1551_);
                    return v___x_1553_;
                } else {
                    lean_dec_ref(v_x_1551_);
                    v_val_1554_ = lean_ctor_get(v___x_1552_, 0);
                    v_isSharedCheck_1562_ = (!lean_is_exclusive(v___x_1552_)) as u8;
                    if v_isSharedCheck_1562_ == 0 {
                        v___x_1556_ = v___x_1552_;
                        v_isShared_1557_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1554_);
                        lean_dec(v___x_1552_);
                        v___x_1556_ = lean_box(0);
                        v_isShared_1557_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1558_ = l_Lean_Omega_normalize(v_val_1554_);
                if v_isShared_1557_ == 0 {
                    lean_ctor_set(v___x_1556_, 0, v___x_1558_);
                    v___x_1560_ = v___x_1556_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_tidy(mut v_p_1563_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_p_1563_);
    v___x_1564_ = l_Lean_Omega_tidy_x3f(v_p_1563_);
    if lean_obj_tag(v___x_1564_) == 0 {
        return v_p_1563_;
    } else {
        let mut v_val_1565_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_1563_);
        v_val_1565_ = lean_ctor_get(v___x_1564_, 0);
        lean_inc(v_val_1565_);
        lean_dec_ref_known(v___x_1564_, 1);
        return v_val_1565_;
    }
}
pub unsafe fn l_Lean_Omega_tidyConstraint(
    mut v_s_1566_: *mut LeanObject,
    mut v_x_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1570_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1568_, 0, v_s_1566_);
    lean_ctor_set(v___x_1568_, 1, v_x_1567_);
    v___x_1569_ = l_Lean_Omega_tidy(v___x_1568_);
    v_fst_1570_ = lean_ctor_get(v___x_1569_, 0);
    lean_inc(v_fst_1570_);
    lean_dec_ref(v___x_1569_);
    return v_fst_1570_;
}
pub unsafe fn l_Lean_Omega_tidyCoeffs(
    mut v_s_1571_: *mut LeanObject,
    mut v_x_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1575_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1573_, 0, v_s_1571_);
    lean_ctor_set(v___x_1573_, 1, v_x_1572_);
    v___x_1574_ = l_Lean_Omega_tidy(v___x_1573_);
    v_snd_1575_ = lean_ctor_get(v___x_1574_, 1);
    lean_inc(v_snd_1575_);
    lean_dec_ref(v___x_1574_);
    return v_snd_1575_;
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(
    mut v_x_1576_: *mut LeanObject,
    mut v_h__1_1577_: *mut LeanObject,
    mut v_h__2_1578_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1576_) == 0 {
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1578_);
        v___x_1579_ = lean_box(0);
        v___x_1580_ = lean_apply_1(v_h__1_1577_, v___x_1579_);
        return v___x_1580_;
    } else {
        let mut v_val_1581_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1582_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1577_);
        v_val_1581_ = lean_ctor_get(v_x_1576_, 0);
        lean_inc(v_val_1581_);
        lean_dec_ref_known(v_x_1576_, 1);
        v_fst_1582_ = lean_ctor_get(v_val_1581_, 0);
        lean_inc(v_fst_1582_);
        v_snd_1583_ = lean_ctor_get(v_val_1581_, 1);
        lean_inc(v_snd_1583_);
        lean_dec(v_val_1581_);
        v___x_1584_ = lean_apply_2(v_h__2_1578_, v_fst_1582_, v_snd_1583_);
        return v___x_1584_;
    }
}
pub unsafe fn l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter(
    mut v_motive_1585_: *mut LeanObject,
    mut v_x_1586_: *mut LeanObject,
    mut v_h__1_1587_: *mut LeanObject,
    mut v_h__2_1588_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1586_) == 0 {
        let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1588_);
        v___x_1589_ = lean_box(0);
        v___x_1590_ = lean_apply_1(v_h__1_1587_, v___x_1589_);
        return v___x_1590_;
    } else {
        let mut v_val_1591_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1592_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1587_);
        v_val_1591_ = lean_ctor_get(v_x_1586_, 0);
        lean_inc(v_val_1591_);
        lean_dec_ref_known(v_x_1586_, 1);
        v_fst_1592_ = lean_ctor_get(v_val_1591_, 0);
        lean_inc(v_fst_1592_);
        v_snd_1593_ = lean_ctor_get(v_val_1591_, 1);
        lean_inc(v_snd_1593_);
        lean_dec(v_val_1591_);
        v___x_1594_ = lean_apply_2(v_h__2_1588_, v_fst_1592_, v_snd_1593_);
        return v___x_1594_;
    }
}
pub unsafe fn l_Lean_Omega_bmod__div__term___lam__0(
    mut v_m_1595_: *mut LeanObject,
    mut v_x_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Int_bmod(v_x_1596_, v_m_1595_);
    return v___x_1597_;
}
pub unsafe fn l_Lean_Omega_bmod__div__term___lam__0___boxed(
    mut v_m_1598_: *mut LeanObject,
    mut v_x_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Lean_Omega_bmod__div__term___lam__0(v_m_1598_, v_x_1599_);
    lean_dec(v_x_1599_);
    return v_res_1600_;
}
pub unsafe fn l_Lean_Omega_bmod__div__term(
    mut v_m_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_b_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_m_1601_, 2);
    v___f_1604_ = lean_alloc_closure(
        l_Lean_Omega_bmod__div__term___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1604_, 0, v_m_1601_);
    lean_inc(v_b_1603_);
    v___x_1605_ = l_Lean_Omega_IntList_dot(v_a_1602_, v_b_1603_);
    v___x_1606_ = l_Int_bmod(v___x_1605_, v_m_1601_);
    lean_dec(v___x_1605_);
    v___x_1607_ = lean_box(0);
    v___x_1608_ = l_List_mapTR_loop___redArg(v___f_1604_, v_a_1602_, v___x_1607_);
    v___x_1609_ = l_Lean_Omega_IntList_dot(v___x_1608_, v_b_1603_);
    lean_dec(v___x_1608_);
    v___x_1610_ = lean_int_sub(v___x_1606_, v___x_1609_);
    lean_dec(v___x_1609_);
    lean_dec(v___x_1606_);
    v___x_1611_ = lean_nat_to_int(v_m_1601_);
    v___x_1612_ = lean_int_ediv(v___x_1610_, v___x_1611_);
    lean_dec(v___x_1611_);
    lean_dec(v___x_1610_);
    return v___x_1612_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(
    mut v_m_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1614_) == 0 {
                    lean_dec(v_m_1613_);
                    v___x_1616_ = l_List_reverse___redArg(v_a_1615_);
                    return v___x_1616_;
                } else {
                    v_head_1617_ = lean_ctor_get(v_a_1614_, 0);
                    v_tail_1618_ = lean_ctor_get(v_a_1614_, 1);
                    v_isSharedCheck_1627_ = (!lean_is_exclusive(v_a_1614_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1620_ = v_a_1614_;
                        v_isShared_1621_ = v_isSharedCheck_1627_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1618_);
                        lean_inc(v_head_1617_);
                        lean_dec(v_a_1614_);
                        v___x_1620_ = lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1627_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_m_1613_);
                v___x_1622_ = l_Int_bmod(v_head_1617_, v_m_1613_);
                lean_dec(v_head_1617_);
                if v_isShared_1621_ == 0 {
                    lean_ctor_set(v___x_1620_, 1, v_a_1615_);
                    lean_ctor_set(v___x_1620_, 0, v___x_1622_);
                    v___x_1624_ = v___x_1620_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1622_);
                    lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_a_1615_);
                    v___x_1624_ = v_reuseFailAlloc_1626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1614_ = v_tail_1618_;
                v_a_1615_ = v___x_1624_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_bmod__coeffs(
    mut v_m_1628_: *mut LeanObject,
    mut v_i_1629_: *mut LeanObject,
    mut v_x_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1631_ = lean_box(0);
    lean_inc(v_m_1628_);
    v___x_1632_ = l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(
        v_m_1628_,
        v_x_1630_,
        v___x_1631_,
    );
    v___x_1633_ = lean_nat_to_int(v_m_1628_);
    v___x_1634_ = l_Lean_Omega_IntList_set(v___x_1632_, v_i_1629_, v___x_1633_);
    return v___x_1634_;
}
pub unsafe fn l_Lean_Omega_bmod__coeffs___boxed(
    mut v_m_1635_: *mut LeanObject,
    mut v_i_1636_: *mut LeanObject,
    mut v_x_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1638_: *mut LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Lean_Omega_bmod__coeffs(v_m_1635_, v_i_1636_, v_x_1637_);
    lean_dec(v_i_1636_);
    return v_res_1638_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Omega_Constraint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Omega_Coeffs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Omega_Constraint_impossible = _init_l_Lean_Omega_Constraint_impossible();
    lean_mark_persistent(l_Lean_Omega_Constraint_impossible);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Omega_Constraint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Omega_Constraint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Omega_Coeffs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega_Constraint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Omega_Constraint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Omega_Constraint(builtin);
}
